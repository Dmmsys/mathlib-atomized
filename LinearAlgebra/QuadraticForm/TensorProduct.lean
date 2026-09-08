/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The quadratic form on a tensor product

## Main definitions

* `QuadraticForm.tensorDistrib (Q₁ ⊗ₜ Q₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `Q₁` on `M₁` and `Q₂` on `M₂`. This construction is not available in characteristic two.

-/

@[expose] public section

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open LinearMap (BilinMap BilinForm)
open TensorProduct QuadraticMap

section CommRing
variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

section InvertibleTwo
variable [Invertible (2 : R)]

namespace QuadraticMap

variable (R A) in
/-- The tensor product of two quadratic maps injects into quadratic maps on tensor products.

Note this is heterobasic; the quadratic map on the left can take values in a module over a larger
ring than the one on the right. -/
/-
**QuadraticMap.tensorDistrib** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：tensorDistrib : QuadraticMap A M₁ N₁ otimes[R] QuadraticMap R M₂ N₂ ->ₗ[A]
 QuadraticMap A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two quadratic maps injects into quadratic maps on tensor p
roducts.

Note this is heterobasic; the quadratic map on the left can take values in a mod
ule over a larger
ring than the one on the right.
-/
def tensorDistrib :
    QuadraticMap A M₁ N₁ ⊗[R] QuadraticMap R M₂ N₂ →ₗ[A] QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ →ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ →ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB

@[simp]
/-
**QuadraticMap.tensorDistrib_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：tensorDistrib_tmul (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂)
 (m₁ : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ otimesₜ Q₂) (m₁ otimesₜ m₂) = Q₁ m₁
 otimesₜ Q₂ m₂
参数：Q₁ : QuadraticMap A M₁ N₁；Q₂ : QuadraticMap R M₂ N₂；m₁ : M₁；m₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinMap.tensorDistrib_tmul`：tensorDistrib_tmul (B₁ : BilinMap
 A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) : te
nsorDistrib R A (B₁ otimesₜ…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x
-/
theorem tensorDistrib_tmul (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) (m₁ : M₁)
    (m₂ : M₂) : tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₁ m₁ ⊗ₜ Q₂ m₂ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic maps, a shorthand for dot notation. -/
/-
**QuadraticMap.tmul** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type uR} →   {A : Type uA} →     {M₁ : Type uM₁} →       {M₂ : Type u
M₂} →         {N₁ : Type uN₁} →           {N₂ : Type uN₂} →             [inst : 
CommRing R] →               [inst_1 : CommRing A] →                 [inst_2 : Ad
dCommGroup M₁] →                   [inst_3 : AddCommGroup M₂] →                 
    [inst_4 : AddCommGroup N₁] →                       [inst_5 : AddCommGroup N₂
] →                         [inst_6 : Algebra R A] →                           [
inst_7 : _root_.Module R M₁] →                             [inst_8 : _root_.Modu
le A M₁] →                               [inst_9 : _root_.Module R N₁] →        
                         [inst_10 : _root_.Module A N₁] →                       
            [inst_11 : SMulCommClass R A M₁] →                                  
   [IsScalarTower R A M₁] →                                       [inst_13 : IsS
calarTower R A N₁] →                                         [inst_14 : _root_.M
odule R M₂] →                                           [inst_15 : _root_.Module
 R N₂] →                                             [Invertible 2] →           
                                    QuadraticMap A M₁ N₁ →                      
                           QuadraticMap R M₂ N₂ →                               
                    QuadraticMap A (TensorProduct R M₁ M₂) (TensorProduct R N₁ N
₂)
参数：TensorProduct R M₁ M₂；TensorProduct R N₁ N₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two quadratic maps, a shorthand for dot notation.
-/
protected abbrev tmul (Q₁ : QuadraticMap A M₁ N₁)
    (Q₂ : QuadraticMap R M₂ N₂) : QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  tensorDistrib R A (Q₁ ⊗ₜ[R] Q₂)
/-
**QuadraticMap.associated_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : Qua
draticMap R M₂ N₂) : (Q₁.tmul Q₂).associated = Q₁.associated.tmul Q₂.associated
参数：2 : A；Q₁ : QuadraticMap A M₁ N₁；Q₂ : QuadraticMap R M₂ N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.tmul.eq_1`：∀ {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M
₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂} [inst : CommRing R]   [inst_1 : Co
mmRing A] [i…
· 使用定理 `LinearMap.BilinMap.tmul.eq_1`：∀ {R : Type uR} {A : Type uA} {M₁ : Type u
M₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂} [inst : CommSemiring R]   [i
nst_1 : CommSemiri…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `QuadraticMap.associated_left_inverse`：associated_left_inverse {B₁ : Bili
nMap R M N} (h : forall x y, B₁ x y = B₁ y x) : associatedHom S B₁.toQuadraticMa
p = B₁
· 使用引理 `LinearMap.BilinMap.tmul_isSymm`：tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ 
: BilinMap R M₂ N₂} (hB₁ : forall x y, B₁ x y = B₁ y x) (hB₂ : forall x y, B₂ x 
y = B₂ y x) (x y : M…
· 使用定理 `QuadraticMap.associated_isSymm`：associated_isSymm (Q : QuadraticMap R M 
N) (x y : M) : associatedHom S Q x y = associatedHom S Q y x
-/
theorem associated_tmul [Invertible (2 : A)]
    (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) :
    (Q₁.tmul Q₂).associated = Q₁.associated.tmul Q₂.associated := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.tmul, BilinMap.tmul]
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert!
    associated_left_inverse A
      (LinearMap.BilinMap.tmul_isSymm (QuadraticMap.associated_isSymm A Q₁)
        (QuadraticMap.associated_isSymm R Q₂))

end QuadraticMap

namespace QuadraticForm

variable (R A) in
/-- The tensor product of two quadratic forms injects into quadratic forms on tensor products.

Note this is heterobasic; the quadratic form on the left can take values in a larger ring than
the one on the right. -/
/-
**QuadraticForm.tensorDistrib** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：tensorDistrib : QuadraticForm A M₁ otimes[R] QuadraticForm R M₂ ->ₗ[A] Qua
draticForm A (M₁ otimes[R] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two quadratic forms injects into quadratic forms on tensor
 products.

Note this is heterobasic; the quadratic form on the left can take values in a la
rger ring than
the one on the right.
-/
def tensorDistrib :
    QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrQuadraticMap.toLinearMap ∘ₗ QuadraticMap.tensorDistrib R A

-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
/-
**QuadraticForm.tensorDistrib_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁
 : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ otimesₜ Q₂) (m₁ otimesₜ m₂) = Q₂ m₂ • Q
₁ m₁
参数：Q₁ : QuadraticForm A M₁；Q₂ : QuadraticForm R M₂；m₁ : M₁；m₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LinearMap.BilinForm.tensorDistrib_tmul`：tensorDistrib_tmul (B₁ : BilinFo
rm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) : tenso
rDistrib R A (B₁ otimesₜ B₂)…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x
-/
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) :
    tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₂ m₂ • Q₁ m₁ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (LinearMap.BilinForm.tensorDistrib_tmul _ _ _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic forms, a shorthand for dot notation. -/
/-
**QuadraticForm.tmul** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：{R : Type uR} →   {A : Type uA} →     {M₁ : Type uM₁} →       {M₂ : Type u
M₂} →         [inst : CommRing R] →           [inst_1 : CommRing A] →           
  [inst_2 : AddCommGroup M₁] →               [inst_3 : AddCommGroup M₂] →       
          [inst_4 : Algebra R A] →                   [inst_5 : _root_.Module R M
₁] →                     [inst_6 : _root_.Module A M₁] →                       [
inst_7 : SMulCommClass R A M₁] →                         [IsScalarTower R A M₁] 
→                           [inst_9 : _root_.Module R M₂] →                     
        [Invertible 2] →                               QuadraticForm A M₁ → Quad
raticForm R M₂ → QuadraticForm A (TensorProduct R M₁ M₂)
参数：TensorProduct R M₁ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two quadratic forms, a shorthand for dot notation.
-/
protected abbrev tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib R A (Q₁ ⊗ₜ[R] Q₂)
/-
**QuadraticForm.associated_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : Quadr
aticForm R M₂) : (Q₁.tmul Q₂).associated = BilinForm.tmul Q₁.associated Q₂.assoc
iated
参数：2 : A；Q₁ : QuadraticForm A M₁；Q₂ : QuadraticForm R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.tmul.eq_1`：∀ {R : Type uR} {A : Type uA} {M₁ : Type 
uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2
 : AddCommMonoid M₁…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.BilinForm.tensorDistrib.eq_1`：∀ (R : Type uR) (A : Type uA) {M
₁ : Type uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A] 
  [inst_2 : AddCommMonoid M₁…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinMap.tmul.eq_1`：∀ {R : Type uR} {A : Type uA} {M₁ : Type u
M₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂} [inst : CommSemiring R]   [i
nst_1 : CommSemiri…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `QuadraticMap.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ :
 QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) : (Q₁.tmul Q₂).associated = Q
₁.associated.tmul …
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LinearEquiv.congrRight₂_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ : T
ype u_9} {N₂ : Type…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `QuadraticForm.tensorDistrib_tmul`：tensorDistrib_tmul (Q₁ : QuadraticForm
 A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ oti
mesₜ Q₂) (m₁ otimesₜ m…
· 使用定理 `QuadraticMap.tensorDistrib_tmul`：tensorDistrib_tmul (Q₁ : QuadraticMap A
 M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ 
otimesₜ Q₂) (m₁ otime…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 32 条，此处仅展示前 30 条）
-/
theorem associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).associated = BilinForm.tmul Q₁.associated Q₂.associated := by
  rw [BilinForm.tmul, BilinForm.tensorDistrib, LinearMap.comp_apply, ← BilinMap.tmul,
    ← QuadraticMap.associated_tmul Q₁ Q₂, LinearEquiv.coe_coe, LinearEquiv.congrRight₂_apply]
  ext : 6
  simp [associated_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**QuadraticForm.polarBilin_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：polarBilin_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : Quadr
aticForm R M₂) : polarBilin (Q₁.tmul Q₂) = ⅟(2 : A) • BilinForm.tmul (polarBilin
 Q₁) (polarBilin Q₂)
参数：2 : A；Q₁ : QuadraticForm A M₁；Q₂ : QuadraticForm R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.two_nsmul_associated`：∀ (S : Type u_1) {R : Type u_3} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `LinearMap.BilinForm.tmul.congr_simp`：∀ {R : Type uR} {A : Type uA} {M₁ :
 Type uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [
inst_2 : AddCommMonoid M₁…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `invOf_two_add_invOf_two`：invOf_two_add_invOf_two [NonAssocSemiring R] [I
nvertible (2 : R)] : (⅟2 : R) + (⅟2 : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem polarBilin_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    polarBilin (Q₁.tmul Q₂) = ⅟(2 : A) • BilinForm.tmul (polarBilin Q₁) (polarBilin Q₂) := by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : ℕ), ← smul_assoc, two_smul _ (_ : A), invOf_two_add_invOf_two,
    one_smul]

variable (A) in
/-- The base change of a quadratic form. -/
/-
**QuadraticForm.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：{R : Type uR} →   (A : Type uA) →     {M₂ : Type uM₂} →       [inst : Comm
Ring R] →         [inst_1 : CommRing A] →           [inst_2 : AddCommGroup M₂] →
             [inst_3 : Algebra R A] →               [inst_4 : _root_.Module R M₂
] →                 [Invertible 2] → QuadraticForm R M₂ → QuadraticForm A (Tenso
rProduct R A M₂)
参数：A : Type uA；TensorProduct R A M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change of a quadratic form.
-/
protected def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticMap.sq (R := A)) Q

@[simp]
/-
**QuadraticForm.baseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) : Q.baseChange 
A (a otimesₜ m₂) = Q m₂ • (a * a)
参数：Q : QuadraticForm R M₂；a : A；m₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticForm.tensorDistrib_tmul`：tensorDistrib_tmul (Q₁ : QuadraticForm
 A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ oti
mesₜ Q₂) (m₁ otimesₜ m…
-/
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange A (a ⊗ₜ m₂) = Q m₂ • (a * a) :=
  tensorDistrib_tmul _ _ _ _
/-
**QuadraticForm.associated_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：associated_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) : asso
ciated (R
参数：2 : A；Q : QuadraticForm R M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用引理 `QuadraticMap.associated_sq`：associated_sq [Invertible (2 : R)] : associa
ted (R
-/
theorem associated_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    associated (R := A) (Q.baseChange A) = BilinForm.baseChange A (associated (R := R) Q) := by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticMap.sq (R := A)) Q, associated_sq]
  exact rfl
/-
**QuadraticForm.polarBilin_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：polarBilin_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) : pola
rBilin (Q.baseChange A) = BilinForm.baseChange A (polarBilin Q)
参数：2 : A；Q : QuadraticForm R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticForm.baseChange.eq_1`：∀ {R : Type uR} (A : Type uA) {M₂ : Type 
uM₂} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup M₂]   [ins
t_3 : Algebra R A] …
· 使用定理 `LinearMap.BilinForm.baseChange.eq_1`：∀ {R : Type uR} (A : Type uA) {M₂ :
 Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddComm
Monoid M₂] [inst_3 : Alge…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticForm.polarBilin_tmul`：polarBilin_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : polarBilin (Q₁.tmul Q₂) = ⅟(2 
: A) • BilinForm.tm…
· 使用定理 `LinearMap.BilinForm.tmul.eq_1`：∀ {R : Type uR} {A : Type uA} {M₁ : Type 
uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2
 : AddCommMonoid M₁…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `QuadraticMap.two_nsmul_associated`：∀ (S : Type u_1) {R : Type u_3} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `QuadraticMap.coe_associatedHom`：coe_associatedHom : ⇑(associatedHom S : 
QuadraticMap R M N ->ₗ[S] BilinMap R M N) = associated
· 使用引理 `QuadraticMap.associated_sq`：associated_sq [Invertible (2 : R)] : associa
ted (R
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `invOf_two_add_invOf_two`：invOf_two_add_invOf_two [NonAssocSemiring R] [I
nvertible (2 : R)] : (⅟2 : R) + (⅟2 : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem polarBilin_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    polarBilin (Q.baseChange A) = BilinForm.baseChange A (polarBilin Q) := by
  rw [QuadraticForm.baseChange, BilinForm.baseChange, polarBilin_tmul, BilinForm.tmul,
    ← map_smul, smul_tmul', ← two_nsmul_associated R, coe_associatedHom, associated_sq,
    smul_comm, ← smul_assoc, two_smul, invOf_two_add_invOf_two, one_smul]

end QuadraticForm

end InvertibleTwo

set_option backward.defeqAttrib.useBackward true in
/-- If two quadratic maps from `A ⊗[R] M₂` agree on elements of the form `1 ⊗ m`, they are equal.

In other words, if a base change exists for a quadratic map, it is unique.

Note that unlike `QuadraticForm.baseChange`, this does not need `Invertible (2 : R)`. -/
@[ext]
/-
**baseChange_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：baseChange_ext ⦃Q₁ Q₂ : QuadraticMap A (A otimes[R] M₂) N₁⦄ (h : forall m,
 Q₁ (1 otimesₜ m) = Q₂ (1 otimesₜ m)) : Q₁ = Q₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
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
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If two quadratic maps from `A ⊗[R] M₂` agree on elements of the form `1 ⊗ m`, th
ey are equal.

In other words, if a base change exists for a quadratic map, it is unique.

Note that unlike `QuadraticForm.baseChange`, this does not need `Invertible (2 :
 R)`.
-/
theorem baseChange_ext ⦃Q₁ Q₂ : QuadraticMap A (A ⊗[R] M₂) N₁⦄
    (h : ∀ m, Q₁ (1 ⊗ₜ m) = Q₂ (1 ⊗ₜ m)) :
    Q₁ = Q₂ := by
  replace h (a m) : Q₁ (a ⊗ₜ m) = Q₂ (a ⊗ₜ m) := by
    rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', QuadraticMap.map_smul, QuadraticMap.map_smul, h]
  ext x
  induction x with
  | tmul => simp [h]
  | zero => simp
  | add x y hx hy =>
    have : Q₁.polarBilin = Q₂.polarBilin := by
      ext
      dsimp [polar]
      rw [← TensorProduct.tmul_add, h, h, h]
    replace := congr($this x y)
    dsimp [polar] at this
    linear_combination (norm := module) this + hx + hy

end CommRing

