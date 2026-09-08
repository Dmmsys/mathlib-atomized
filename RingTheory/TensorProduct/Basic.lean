/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# The tensor product of R-algebras

This file provides results about the multiplicative structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

- `Algebra.TensorProduct.semiring`: the ring structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

@[expose] public section

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct


namespace LinearMap

section liftBaseChange

variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

/--
If `M` is an `R`-module and `N` is an `A`-module, then `A`-linear maps `A ⊗[R] M →ₗ[A] N`
correspond to `R` linear maps `M →ₗ[R] N` by composing with `M → A ⊗ M`, `x ↦ 1 ⊗ x`.
-/
/-
**LinearMap.liftBaseChangeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：liftBaseChangeEquiv : (M ->ₗ[R] N) ≃ₗ[A] (A otimes[R] M ->ₗ[A] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is an `R`-module and `N` is an `A`-module, then `A`-linear maps `A ⊗[R] M
 →ₗ[A] N`
correspond to `R` linear maps `M →ₗ[R] N` by composing with `M → A ⊗ M`, `x ↦ 1 
⊗ x`.
-/
def liftBaseChangeEquiv : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

/-- If `N` is an `A` module, we may lift a linear map `M →ₗ[R] N` to `A ⊗[R] M →ₗ[A] N` -/
/-
**LinearMap.liftBaseChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap`。
形式化陈述：liftBaseChange (l : M ->ₗ[R] N) : A otimes[R] M ->ₗ[A] N
参数：l : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is an `A` module, we may lift a linear map `M →ₗ[R] N` to `A ⊗[R] M →ₗ[A]
 N`
-/
abbrev liftBaseChange (l : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l

@[simp]
/-
**LinearMap.liftBaseChange_tmul** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：liftBaseChange_tmul (l : M ->ₗ[R] N) (x y) : l.liftBaseChange A (x otimesₜ
 y) = x • l y
参数：l : M ->ₗ[R] N；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma liftBaseChange_tmul (l : M →ₗ[R] N) (x y) : l.liftBaseChange A (x ⊗ₜ y) = x • l y := rfl
/-
**LinearMap.liftBaseChange_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：liftBaseChange_one_tmul (l : M ->ₗ[R] N) (y) : l.liftBaseChange A (1 otime
sₜ y) = l y
参数：l : M ->ₗ[R] N；y。
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftBaseChange_one_tmul (l : M →ₗ[R] N) (y) : l.liftBaseChange A (1 ⊗ₜ y) = l y := by simp

@[simp]
/-
**LinearMap.liftBaseChangeEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
形式化陈述：liftBaseChangeEquiv_symm_apply (l : A otimes[R] M ->ₗ[A] N) (x) : (liftBas
eChangeEquiv A).symm l x = l (1 otimesₜ x)
参数：l : A otimes[R] M ->ₗ[A] N；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma liftBaseChangeEquiv_symm_apply (l : A ⊗[R] M →ₗ[A] N) (x) :
    (liftBaseChangeEquiv A).symm l x = l (1 ⊗ₜ x) := rfl
/-
**LinearMap.liftBaseChange_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsSca
larTower R A P] (l : M ->ₗ[R] N) (l' : N ->ₗ[A] P) : l' ∘ₗ l.liftBaseChange A = 
(l'.restrictScalars R ∘ₗ l).liftBaseChange A
参数：l : M ->ₗ[R] N；l' : N ->ₗ[A] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
    (l : M →ₗ[R] N) (l' : N →ₗ[A] P) :
      l' ∘ₗ l.liftBaseChange A = (l'.restrictScalars R ∘ₗ l).liftBaseChange A := by
  ext
  simp

@[simp]
/-
**LinearMap.range_liftBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_liftBaseChange (l : M ->ₗ[R] N) : LinearMap.range (l.liftBaseChange 
A) = Submodule.span A (LinearMap.range l)
参数：l : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `LinearMap.liftBaseChange_tmul`：liftBaseChange_tmul (l : M ->ₗ[R] N) (x y
) : l.liftBaseChange A (x otimesₜ y) = x • l y
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_liftBaseChange (l : M →ₗ[R] N) :
    LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩

end liftBaseChange

end LinearMap

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

section AddCommMonoidWithOne

variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1
/-
**Algebra.TensorProduct.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct
`。
形式化陈述：one_def : (1 : A otimes[R] B) = (1 : A) otimesₜ (1 : B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
/-
**Algebra.TensorProduct.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Alge
bra.TensorProduct`。
形式化陈述：instAddCommMonoidWithOne : AddCommMonoidWithOne (A otimes[R] B) where natC
ast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne (A ⊗[R] B) where
  natCast n := n ⊗ₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm
/-
**Algebra.TensorProduct.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：natCast_def (n : Nat) : (n : A otimes[R] B) = (n : A) otimesₜ (1 : B)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl
/-
**Algebra.TensorProduct.natCast_def'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：natCast_def' (n : Nat) : (n : A otimes[R] B) = (1 : A) otimesₜ (n : B)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.natCast_def`：natCast_def (n : Nat) : (n : A otimes
[R] B) = (n : A) otimesₜ (1 : B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
theorem natCast_def' (n : ℕ) : (n : A ⊗[R] B) = (1 : A) ⊗ₜ (n : B) := by
  rw [natCast_def, ← nsmul_one, smul_tmul, nsmul_one]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
@[irreducible]
/-
**Algebra.TensorProduct.mul** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：mul : A otimes[R] B ->ₗ[R] A otimes[R] B ->ₗ[R] A otimes[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

unseal mul in
@[simp]
/-
**Algebra.TensorProduct.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：mul_apply (a₁ a₂ : A) (b₁ b₂ : B) : mul (a₁ otimesₜ[R] b₁) (a₂ otimesₜ[R] 
b₂) = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
参数：a₁ a₂ : A；b₁ b₂ : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

-- providing this instance separately makes some downstream code substantially faster
/-
**Algebra.TensorProduct.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct
`。
形式化陈述：instMul : Mul (A otimes[R] B) where mul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (A ⊗[R] B) where
  mul a b := mul a b

unseal mul in
@[simp]
/-
**Algebra.TensorProduct.tmul_mul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b
₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
参数：a₁ a₂ : A；b₁ b₂ : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

unseal mul in
/-
**Algebra.TensorProduct._root_.SemiconjBy.tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SemiconjBy.tmul {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha : SemiconjBy a₁ a₂ a₃) (hb : SemiconjBy b₁ b₂ b₃) :
    SemiconjBy (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃) :=
  congr_arg₂ (· ⊗ₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) :=
  ha.tmul hb
/-
**Algebra.TensorProduct.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 
`Algebra.TensorProduct`。
形式化陈述：instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A otimes[R] B) 
where left_distrib a b c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

-- we want `isScalarTower_right` to take priority since it's better for unification elsewhere
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isScalarTower_right [Monoid S] [DistribMulAction S A]
    [IsScalarTower S A A] [SMulCommClass R S A] : IsScalarTower S (A ⊗[R] B) (A ⊗[R] B) where
  smul_assoc r x y := by
    change r • x * y = r • (x * y)
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, smul_mul_assoc]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

-- we want `Algebra.to_smulCommClass` to take priority since it's better for unification elsewhere
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sMulCommClass_right [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [SMulCommClass R S A] : SMulCommClass S (A ⊗[R] B) (A ⊗[R] B) where
  smul_comm r x y := by
    change r • (x * y) = x * r • y
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, mul_smul_comm]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [CommSemiring R]
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-
**Algebra.TensorProduct.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct
`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_
1 : NonAssocSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass R
 A A] [inst_4 : IsScalarTower R A A]   [inst_5 : NonAssocSemiring B] [inst_6 : _
root_.Module R B] [inst_7 : SMulCommClass R B B]   [inst_8 : IsScalarTower R B B
] (x : TensorProduct R A B), (Algebra.TensorProduct.mul (1 ⊗ₜ[R] 1)) x = x
参数：x : TensorProduct R A B；Algebra.TensorProduct.mul (1 ⊗ₜ[R] 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
protected theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
/-
**Algebra.TensorProduct.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct
`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_
1 : NonAssocSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass R
 A A] [inst_4 : IsScalarTower R A A]   [inst_5 : NonAssocSemiring B] [inst_6 : _
root_.Module R B] [inst_7 : SMulCommClass R B B]   [inst_8 : IsScalarTower R B B
] (x : TensorProduct R A B), (Algebra.TensorProduct.mul x) (1 ⊗ₜ[R] 1) = x
参数：x : TensorProduct R A B；Algebra.TensorProduct.mul x；1 ⊗ₜ[R] 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
/-
**Algebra.TensorProduct.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：instNonAssocSemiring : NonAssocSemiring (A otimes[R] B) where one_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.one_mul`：∀ {R : Type uR} {A : Type uA} {B : Type u
B} [inst : CommSemiring R] [inst_1 : NonAssocSemiring A]   [inst_2 : _root_.Modu
le R A] [inst_3 : S…
· 使用定理 `Algebra.TensorProduct.mul_one`：∀ {R : Type uR} {A : Type uA} {B : Type u
B} [inst : CommSemiring R] [inst_1 : NonAssocSemiring A]   [inst_2 : _root_.Modu
le R A] [inst_3 : S…
-/
instance instNonAssocSemiring : NonAssocSemiring (A ⊗[R] B) where
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

end NonAssocSemiring

section NonUnitalSemiring
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

unseal mul in
/-
**Algebra.TensorProduct.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_
1 : NonUnitalSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : SMulCommClass 
R A A] [inst_4 : IsScalarTower R A A]   [inst_5 : NonUnitalSemiring B] [inst_6 :
 _root_.Module R B] [inst_7 : SMulCommClass R B B]   [inst_8 : IsScalarTower R B
 B] (x y z : TensorProduct R A B),   (Algebra.TensorProduct.mul ((Algebra.Tensor
Product.mul x) y)) z =     (Algebra.TensorProduct.mul x) ((Algebra.TensorProduct
.mul y) z)
参数：x y z : TensorProduct R A B；Algebra.TensorProduct.mul ((Algebra.TensorProduct
.mul x) y)；Algebra.TensorProduct.mul x；(Algebra.TensorProduct.mul y) z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· ⊗ₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)
/-
**Algebra.TensorProduct.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：instNonUnitalSemiring : NonUnitalSemiring (A otimes[R] B) where mul_assoc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.mul_assoc`：∀ {R : Type uR} {A : Type uA} {B : Type
 uB} [inst : CommSemiring R] [inst_1 : NonUnitalSemiring A]   [inst_2 : _root_.M
odule R A] [inst_3 : …
-/
instance instNonUnitalSemiring : NonUnitalSemiring (A ⊗[R] B) where
  mul_assoc := Algebra.TensorProduct.mul_assoc

end NonUnitalSemiring

section Semiring
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]

/-
**Algebra.TensorProduct.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：instSemiring : Semiring (A otimes[R] B) where left_distrib a b c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance instSemiring : Semiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

@[simp]
/-
**Algebra.TensorProduct.tmul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：tmul_pow (a : A) (b : B) (k : Nat) : a otimesₜ[R] b ^ k = (a ^ k) otimesₜ[
R] (b ^ k)
参数：a : A；b : B；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem tmul_pow (a : A) (b : B) (k : ℕ) : a ⊗ₜ[R] b ^ k = (a ^ k) ⊗ₜ[R] (b ^ k) := by
  induction k with
  | zero => simp [one_def]
  | succ k ih => simp [pow_succ, ih]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
/-
**Algebra.TensorProduct.includeLeftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：includeLeftRingHom : A ->+* A otimes[R] B where .toAddMonoidHom __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.
-/
def includeLeftRingHom : A →+* A ⊗[R] B where
  __ := (AlgebraTensorModule.mk R R A B).flip 1 |>.toAddMonoidHom
  map_one' := rfl
  map_mul' := by simp

variable [CommSemiring S] [Algebra S A]

set_option backward.defeqAttrib.useBackward true in
/-
**Algebra.TensorProduct.leftAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：leftAlgebra [SMulCommClass R S A] : Algebra S (A otimes[R] B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=
  { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', ← one_def, mul_smul_comm, smul_mul_assoc, mul_one,
        one_mul]
    smul_def' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc, ← one_def, one_mul]
    algebraMap := TensorProduct.includeLeftRingHom.comp (algebraMap S A) }
/-
**Algebra.TensorProduct.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：algebraMap_def [SMulCommClass R S A] : algebraMap S (A otimes[R] B) = incl
udeLeftRingHom.comp (algebraMap S A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_def [SMulCommClass R S A] :
    algebraMap S (A ⊗[R] B) = includeLeftRingHom.comp (algebraMap S A) := rfl
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个示例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Semiring.toNatAlgebra : Algebra ℕ (ℕ ⊗[ℕ] B)) = leftAlgebra := rfl

-- This is for the `undergrad.yaml` list.
/-- The tensor product of two `R`-algebras is an `R`-algebra. -/
/-
**Algebra.TensorProduct.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：instAlgebra : Algebra R (A otimes[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two `R`-algebras is an `R`-algebra.
-/
instance instAlgebra : Algebra R (A ⊗[R] B) :=
  inferInstance

@[simp]
/-
**Algebra.TensorProduct.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：algebraMap_apply [SMulCommClass R S A] (r : S) : algebraMap S (A otimes[R]
 B) r = (algebraMap S A) r otimesₜ 1
参数：r : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply [SMulCommClass R S A] (r : S) :
    algebraMap S (A ⊗[R] B) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl
/-
**Algebra.TensorProduct.algebraMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：algebraMap_apply' (r : R) : algebraMap R (A otimes[R] B) r = 1 otimesₜ alg
ebraMap R B r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.algebraMap_apply`：algebraMap_apply [SMulCommClass 
R S A] (r : S) : algebraMap S (A otimes[R] B) r = (algebraMap S A) r otimesₜ 1
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
theorem algebraMap_apply' (r : R) :
    algebraMap R (A ⊗[R] B) r = 1 ⊗ₜ algebraMap R B r := by
  rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

/-- The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
/-
**Algebra.TensorProduct.includeLeft** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：includeLeft [SMulCommClass R S A] : A ->ₐ[S] A otimes[R] B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.
-/
def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=
  { includeLeftRingHom with commutes' := by simp }

@[simp]
/-
**Algebra.TensorProduct.includeLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：includeLeft_apply [SMulCommClass R S A] (a : A) : (includeLeft : A ->ₐ[S] 
A otimes[R] B) a = a otimesₜ 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem includeLeft_apply [SMulCommClass R S A] (a : A) :
    (includeLeft : A →ₐ[S] A ⊗[R] B) a = a ⊗ₜ 1 :=
  rfl
/-
**Algebra.TensorProduct.toLinearMap_includeLeft** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.TensorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : Semiring B] [in
st_4 : Algebra R B] [inst_5 : CommSemiring S] [inst_6 : Algebra S A]   [inst_7 :
 SMulCommClass R S A],   Algebra.TensorProduct.includeLeft.toLinearMap = (Tensor
Product.AlgebraTensorModule.mk R S A B).flip 1
参数：TensorProduct.AlgebraTensorModule.mk R S A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearMap_includeLeft [SMulCommClass R S A] :
    (includeLeft : A →ₐ[S] A ⊗[R] B).toLinearMap = (AlgebraTensorModule.mk R S A B).flip 1 := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
/-
**Algebra.TensorProduct.includeRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：includeRight : B ->ₐ[R] A otimes[R] B where .toAddMonoidHom __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`.
-/
def includeRight : B →ₐ[R] A ⊗[R] B where
  __ := AlgebraTensorModule.mk R R A B 1 |>.toAddMonoidHom
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp [algebraMap_eq_smul_one', smul_tmul]

@[simp]
/-
**Algebra.TensorProduct.includeRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：includeRight_apply (b : B) : (includeRight : B ->ₐ[R] A otimes[R] B) b = 1
 otimesₜ b
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem includeRight_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl
/-
**Algebra.TensorProduct.toLinearMap_includeRight** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.TensorProduct`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_
1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] [inst_4 : Algebra
 R B],   Algebra.TensorProduct.includeRight.toLinearMap = (TensorProduct.Algebra
TensorModule.mk R R A B) 1
参数：TensorProduct.AlgebraTensorModule.mk R R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearMap_includeRight :
    (includeRight : B →ₐ[R] A ⊗[R] B).toLinearMap = AlgebraTensorModule.mk R R A B 1 := rfl
/-
**Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap** 是 Mathlib 中的一个定理，位于
命名空间 `Algebra.TensorProduct`。
形式化陈述：includeLeftRingHom_comp_algebraMap : (includeLeftRingHom.comp (algebraMap 
R A) : R ->+* A otimes[R] B) = includeRight.toRingHom.comp (algebraMap R B)
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem includeLeftRingHom_comp_algebraMap :
    (includeLeftRingHom.comp (algebraMap R A) : R →+* A ⊗[R] B) =
      includeRight.toRingHom.comp (algebraMap R B) := by
  ext
  simp

section ext
variable [Algebra R S] [Algebra S C] [IsScalarTower R S A] [IsScalarTower R S C]

/-- A version of `TensorProduct.ext` for `AlgHom`.

Using this as the `@[ext]` lemma instead of `Algebra.TensorProduct.ext'` allows `ext` to apply
lemmas specific to `A →ₐ[S] _` and `B →ₐ[R] _`; notably this allows recursion into nested tensor
products of algebras.

See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**Algebra.TensorProduct.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.comp includeLeft = g.comp inc
ludeLeft) (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).
comp includeRight) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …

--- 原说明 ---
A version of `TensorProduct.ext` for `AlgHom`.

Using this as the `@[ext]` lemma instead of `Algebra.TensorProduct.ext'` allows 
`ext` to apply
lemmas specific to `A →ₐ[S] _` and `B →ₐ[R] _`; notably this allows recursion in
to nested tensor
products of algebras.

See note [partially-applied ext lemmas].
-/
theorem ext ⦃f g : (A ⊗[R] B) →ₐ[S] C⦄
    (ha : f.comp includeLeft = g.comp includeLeft)
    (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).comp includeRight) :
    f = g := by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this
/-
**Algebra.TensorProduct.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：ext' {g h : A otimes[R] B ->ₐ[S] C} (H : forall a b, g (a otimesₜ b) = h (
a otimesₜ b)) : g = h
参数：H : forall a b, g (a otimesₜ b) = h (a otimesₜ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
  ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)

@[ext high]
/-
**Algebra.TensorProduct.ringHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：ringHom_ext {C : Type*} [Semiring C] {f g : A otimes[R] B ->+* C} (h₁ : f.
comp includeLeftRingHom = g.comp includeLeftRingHom) (h₂ : f.comp includeRight.t
oRingHom = g.comp includeRight.toRingHom) : f = g
参数：h₁ : f.comp includeLeftRingHom = g.comp includeLeftRingHom；h₂ : f.comp includ
eRight.toRingHom = g.comp includeRight.toRingHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
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
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma ringHom_ext {C : Type*} [Semiring C] {f g : A ⊗[R] B →+* C}
    (h₁ : f.comp includeLeftRingHom = g.comp includeLeftRingHom)
    (h₂ : f.comp includeRight.toRingHom = g.comp includeRight.toRingHom) : f = g := by
  ext x
  induction x with
  | zero => simp
  | add x y _ _ => simp_all
  | tmul x y => simpa [← map_mul] using congr($h₁ x * $h₂ y)

end ext

end Semiring

section AddCommGroupWithOne
variable [CommSemiring R]
variable [AddCommGroupWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

/-
**Algebra.TensorProduct.instAddCommGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
ra.TensorProduct`。
形式化陈述：instAddCommGroupWithOne : AddCommGroupWithOne (A otimes[R] B) where toAddC
ommGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupWithOne : AddCommGroupWithOne (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z ⊗ₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]
/-
**Algebra.TensorProduct.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：intCast_def (z : Int) : (z : A otimes[R] B) = (z : A) otimesₜ (1 : B)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocRing
variable [CommSemiring R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-
**Algebra.TensorProduct.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebra.TensorProduct`。
形式化陈述：instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A otimes[R] B) where to
AddCommGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

end NonUnitalNonAssocRing

section NonAssocRing
variable [CommSemiring R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-
**Algebra.TensorProduct.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：instNonAssocRing : NonAssocRing (A otimes[R] B) where toAddCommGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing : NonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

end NonAssocRing

section NonUnitalRing
variable [CommSemiring R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-
**Algebra.TensorProduct.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：instNonUnitalRing : NonUnitalRing (A otimes[R] B) where toAddCommGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing : NonUnitalRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

end NonUnitalRing

section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-
**Algebra.TensorProduct.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：instCommSemiring : CommSemiring (A otimes[R] B) where toSemiring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring : CommSemiring (A ⊗[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]

end CommSemiring

section Ring
variable [CommSemiring R]
variable [Ring A] [Algebra R A]
variable [Semiring B] [Algebra R B]

/-
**Algebra.TensorProduct.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：instRing : Ring (A otimes[R] B) where toSemiring
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance instRing : Ring (A ⊗[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing
/-
**Algebra.TensorProduct.intCast_def'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：intCast_def' {B} [Ring B] [Algebra R B] (z : Int) : (z : A otimes[R] B) = 
(1 : A) otimesₜ (z : B)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.intCast_def`：intCast_def (z : Int) : (z : A otimes
[R] B) = (z : A) otimesₜ (1 : B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.int`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Type u_2} {P : Type u_4} [inst_1 : AddCommGroup M]   [inst_2 : AddCommGr
oup P] [inst_3 : _root…
-/
theorem intCast_def' {B} [Ring B] [Algebra R B] (z : ℤ) : (z : A ⊗[R] B) = (1 : A) ⊗ₜ (z : B) := by
  rw [intCast_def, ← zsmul_one, smul_tmul, zsmul_one]

-- verify there are no diamonds
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个示例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
-- fails at `with_reducible_and_instances rfl` https://github.com/leanprover-community/mathlib4/issues/10906
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个示例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Ring.toIntAlgebra _ : Algebra ℤ (ℤ ⊗[ℤ] A)) = leftAlgebra := rfl

end Ring

section CommRing
variable [CommSemiring R]
variable [CommRing A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-
**Algebra.TensorProduct.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：instCommRing : CommRing (A otimes[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing (A ⊗[R] B) :=
  { toRing := inferInstance
    mul_comm := mul_comm }

end CommRing

section RightAlgebra

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-- `S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else the action of
`S` on `S ⊗[R] S` would be ambiguous. -/
/-
**Algebra.TensorProduct.rightAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：rightAlgebra : Algebra B (A otimes[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else th
e action of
`S` on `S ⊗[R] S` would be ambiguous.
-/
abbrev rightAlgebra : Algebra B (A ⊗[R] B) :=
  includeRight.toRingHom.toAlgebra' fun b x => by
    suffices LinearMap.mulLeft R (includeRight b) = LinearMap.mulRight R (includeRight b) from
      congr($this x)
    ext xa xb
    simp [mul_comm]

attribute [local instance] TensorProduct.rightAlgebra
/-
**Algebra.TensorProduct.algebraMap_eq_includeRight** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.TensorProduct`。
形式化陈述：algebraMap_eq_includeRight : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_eq_includeRight :
    letI := rightAlgebra (R := R) (A := A) (B := B)
    algebraMap B (A ⊗[R] B) = includeRight (R := R) (A := A) (B := B) := rfl
/-
**Algebra.TensorProduct.right_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：right_isScalarTower : IsScalarTower R B (A otimes[R] B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
instance right_isScalarTower : IsScalarTower R B (A ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm
/-
**Algebra.TensorProduct.right_algebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：right_algebraMap_apply (b : B) : algebraMap B (A otimes[R] B) b = 1 otimes
ₜ b
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma right_algebraMap_apply (b : B) : algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ b := rfl
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass A B (A ⊗[R] B) where
  smul_comm a b x := x.induction_on (by simp)
    (fun _ _ ↦ by simp [Algebra.smul_def, right_algebraMap_apply, smul_tmul'])
    fun _ _ h₁ h₂ ↦ by simpa using congr($h₁ + $h₂)
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass B A (A ⊗[R] B) := .symm ..

end RightAlgebra

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个示例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the CommRing structure on `A ⊗[ℤ] B`
when `A` and `B` are merely `CommRing`s, by treating both as `ℤ`-algebras.
-/
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个示例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that typeclass search finds the CommRing structure on `A ⊗[ℤ] B`
when `A` and `B` are merely `CommRing`s, by treating both as `ℤ`-algebras.
-/
example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance

variable (R A B) in
/-
**Algebra.TensorProduct.closure_range_union_range_eq_top** 是 Mathlib 中的一个引理，位于命名
空间 `Algebra.TensorProduct`。
形式化陈述：closure_range_union_range_eq_top [CommRing R] [Ring A] [Ring B] [Algebra R
 A] [Algebra R B] : Subring.closure (Set.range (Algebra.TensorProduct.includeLef
t : A ->ₐ[R] A otimes[R] B) union Set.range Algebra.TensorProduct.includeRight) 
= ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
lemma closure_range_union_range_eq_top [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] :
    Subring.closure (Set.range (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) ∪
      Set.range Algebra.TensorProduct.includeRight) = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  induction x with
  | zero => exact zero_mem _
  | tmul x y =>
    convert_to (Algebra.TensorProduct.includeLeftRingHom (R := R) x) *
      (Algebra.TensorProduct.includeRight y) ∈ _
    · simp
    · exact mul_mem (Subring.subset_closure (.inl ⟨x, rfl⟩))
        (Subring.subset_closure (.inr ⟨_, rfl⟩))
  | add x y _ _ => exact add_mem ‹_› ‹_›

set_option backward.isDefEq.respectTransparency false in
/-- If `s` generates `T` as an `R`-algebra,
then `{ 1 ⊗ x | x ∈ s }` generates `A ⊗[R] T` as an `A`-algebra. -/
/-
**Algebra.TensorProduct.adjoin_one_tmul_image_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.TensorProduct`。
形式化陈述：adjoin_one_tmul_image_eq_top [CommSemiring R] [CommSemiring A] [Semiring B
] [Algebra R A] [Algebra R B] (s : Set B) (hs : adjoin R s = ⊤) : adjoin A (((1 
: A) otimesₜ[R] ·) '' s) = ⊤
参数：s : Set B；hs : adjoin R s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.toSubmodule_eq_top`：toSubmodule_eq_top {S : Subalgebra R A} : Su
balgebra.toSubmodule S = ⊤ ↔ S = ⊤
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用引理 `Submodule.baseChange_top`：baseChange_top : (⊤ : Submodule R M).baseChang
e A = ⊤
· 使用引理 `Submodule.baseChange_eq_span`：baseChange_eq_span : p.baseChange A = span
 A (p.map (TensorProduct.mk R A M 1))
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Algebra.span_le_adjoin`：span_le_adjoin (s : Set A) : span R s <= Subalge
bra.toSubmodule (adjoin R s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Algebra.adjoin_adjoin_of_tower`：adjoin_adjoin_of_tower (s : Set A) : adj
oin S (adjoin R s : Set A) = adjoin S s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` generates `T` as an `R`-algebra,
then `{ 1 ⊗ x | x ∈ s }` generates `A ⊗[R] T` as an `A`-algebra.
-/
lemma adjoin_one_tmul_image_eq_top [CommSemiring R] [CommSemiring A]
    [Semiring B] [Algebra R A] [Algebra R B]
    (s : Set B) (hs : adjoin R s = ⊤) : adjoin A (((1 : A) ⊗ₜ[R] ·) '' s) = ⊤ := by
  suffices h : adjoin A ((⊤ : Subalgebra R B).map (includeRight (A := A)) : Set (A ⊗[R] B)) = ⊤ by
    simp [← h, ← hs, AlgHom.map_adjoin, adjoin_adjoin_of_tower]
  rw [← Algebra.toSubmodule_eq_top, ← top_le_iff, Algebra.map_top, ← Submodule.baseChange_top,
    Submodule.baseChange_eq_span, Submodule.map_top]
  exact span_le_adjoin _ _

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- If `M` is a `B`-module that is also an `A`-module, the canonical map
`M →ₗ[A] B ⊗[A] M` is injective. -/
/-
**Algebra.TensorProduct.mk_one_injective_of_isScalarTower** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.TensorProduct`。
形式化陈述：mk_one_injective_of_isScalarTower (M : Type*) [AddCommMonoid M] [Module R 
M] [Module S M] [IsScalarTower R S M] : Function.Injective (TensorProduct.mk R S
 M 1)
参数：M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` is a `B`-module that is also an `A`-module, the canonical map
`M →ₗ[A] B ⊗[A] M` is injective.
-/
lemma mk_one_injective_of_isScalarTower (M : Type*) [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] :
    Function.Injective (TensorProduct.mk R S M 1) := by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange S LinearMap.id)
  intro m
  simp

end TensorProduct

end Algebra

/-
**Algebra.baseChange_lmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.baseChange_lmul {R B : Type*} [CommSemiring R] [Semiring B] [Algeb
ra R B] {A : Type*} [CommSemiring A] [Algebra R A] (f : B) : (Algebra.lmul R B f
).baseChange A = Algebra.lmul A (A otimes[R] B) (1 otimesₜ f)
参数：f : B。
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
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Algebra.baseChange_lmul {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {A : Type*} [CommSemiring A] [Algebra R A] (f : B) :
    (Algebra.lmul R B f).baseChange A = Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ f) := by
  ext i
  simp

namespace TensorProduct.Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]

/-- An auxiliary definition, used for constructing the `Module (A ⊗[R] B) M` in
`TensorProduct.Algebra.module` below. -/
/-
**TensorProduct.Algebra.moduleAux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.Algeb
ra`。
形式化陈述：moduleAux : A otimes[R] B ->ₗ[R] M ->ₗ[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
An auxiliary definition, used for constructing the `Module (A ⊗[R] B) M` in
`TensorProduct.Algebra.module` below.
-/
def moduleAux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B →ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }
/-
**TensorProduct.Algebra.moduleAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
.Algebra`。
形式化陈述：moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a otimesₜ[R] b) m = a
 • b • m
参数：a : A；b : B；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a ⊗ₜ[R] b) m = a • b • m :=
  rfl

variable [SMulCommClass A B M]

/-- If `M` is a representation of two different `R`-algebras `A` and `B` whose actions commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself via left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, `S`. This example
is important because a submodule of `S` as a `Module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a two-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we would have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond but a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itself: one from its
multiplication, and one from this would-be instance. Arguably we could live with this but in any
case the real fix is to address the ambiguity in notation, probably along the lines outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.20base.20change/near/240929258
-/
@[instance_reducible]
/-
**TensorProduct.Algebra.module** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.Algebra`
。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {M : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M] →  
           [inst_2 : _root_.Module R M] →               [inst_3 : Semiring A] → 
                [inst_4 : Semiring B] →                   [inst_5 : _root_.Modul
e A M] →                     [inst_6 : _root_.Module B M] →                     
  [inst_7 : Algebra R A] →                         [inst_8 : Algebra R B] →     
                      [IsScalarTower R A M] →                             [IsSca
larTower R B M] → [SMulCommClass A B M] → _root_.Module (TensorProduct R A B) M
参数：TensorProduct R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of two different `R`-algebras `A` and `B` whose actio
ns commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself v
ia left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, 
`S`. This example
is important because a submodule of `S` as a `Module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a tw
o-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we wo
uld have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond bu
t a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itse
lf: one from its
multiplication, and one from this would-be instance. Arguably we could live with
 this but in any
case the real fix is to address the ambiguity in notation, probably along the li
nes outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.
20base.20change/near/240929258
-/
protected def module : Module (A ⊗[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting note: was one `simp only`, not two
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      -- Porting note: was one `simp only`, not two
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      -- Porting note: was one `simp only`, but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]

attribute [local instance] TensorProduct.Algebra.module
/-
**TensorProduct.Algebra.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.Algebr
a`。
形式化陈述：smul_def (a : A) (b : B) (m : M) : a otimesₜ[R] b • m = a • b • m
参数：a : A；b : B；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl

section Lemmas

/-
**TensorProduct.Algebra.linearMap_comp_mul'** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct.Algebra`。
形式化陈述：linearMap_comp_mul' : Algebra.linearMap R (A otimes[R] B) ∘ₗ LinearMap.mul
' R R = map (Algebra.linearMap R A) (Algebra.linearMap R B)
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
theorem linearMap_comp_mul' :
    Algebra.linearMap R (A ⊗[R] B) ∘ₗ LinearMap.mul' R R =
      map (Algebra.linearMap R A) (Algebra.linearMap R B) := by
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, map_tmul,
    Algebra.linearMap_apply, map_one, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul'_apply, mul_one, Algebra.TensorProduct.one_def]

end Lemmas

end TensorProduct.Algebra

open LinearMap in
/-
**Submodule.map_range_rTensor_subtype_lid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.map_range_rTensor_subtype_lid {R Q} [CommSemiring R] [AddCommMon
oid Q] [Module R Q] {I : Submodule R R} : (range <| rTensor Q I.subtype).map (Te
nsorProduct.lid R Q : R otimes[R] Q ->ₗ[R] Q) = I • ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Submodule.map_range_rTensor_subtype_lid {R Q} [CommSemiring R] [AddCommMonoid Q]
    [Module R Q] {I : Submodule R R} :
    (range <| rTensor Q I.subtype).map (TensorProduct.lid R Q : R ⊗[R] Q →ₗ[R] Q) = I • ⊤ := by
  rw [← map_top, ← Submodule.map_comp, map_top]
  refine le_antisymm ?_ fun q h ↦ Submodule.smul_induction_on h
    (fun r hr q _ ↦ ⟨⟨r, hr⟩ ⊗ₜ q, by simp⟩) (by simp +contextual [add_mem])
  rintro _ ⟨t, rfl⟩
  exact t.induction_on (by simp) (by simp +contextual [Submodule.smul_mem_smul])
    (by simp +contextual [add_mem])

section

variable {R M S T : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring S] [Algebra R S] [Ring T] [Algebra R T]

variable (R S M) in
/-
**TensorProduct.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.mk_surjective (h : Function.Surjective (algebraMap R S)) : F
unction.Surjective (TensorProduct.mk R S M 1)
参数：h : Function.Surjective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
theorem TensorProduct.mk_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact ⟨x • y, rfl⟩

variable (S) in
/-
**TensorProduct.flip_mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.flip_mk_surjective (h : Function.Surjective (algebraMap R T)
) : Function.Surjective ((TensorProduct.mk R S T).flip 1)
参数：h : Function.Surjective (algebraMap R T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
lemma TensorProduct.flip_mk_surjective (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective ((TensorProduct.mk R S T).flip 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨s, t, rfl⟩
  obtain ⟨r, rfl⟩ := h t
  rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul]
  exact ⟨r • s, rfl⟩

variable (T) in
/-
**Algebra.TensorProduct.includeRight_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.includeRight_surjective (h : Function.Surjective (al
gebraMap R S)) : Function.Surjective (includeRight : T ->ₐ[R] S otimes[R] T)
参数：h : Function.Surjective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.mk_surjective`：TensorProduct.mk_surjective (h : Function.S
urjective (algebraMap R S)) : Function.Surjective (TensorProduct.mk R S M 1)
-/
lemma Algebra.TensorProduct.includeRight_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (includeRight : T →ₐ[R] S ⊗[R] T) :=
  TensorProduct.mk_surjective _ _ _ h
/-
**Algebra.TensorProduct.includeLeft_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.includeLeft_surjective (S A : Type*) [CommSemiring S
] [Semiring A] [Algebra S A] [Algebra R A] [SMulCommClass R S A] (h : Function.S
urjective (algebraMap R T)) : Function.Surjective (includeLeft : A ->ₐ[S] A otim
es[R] T)
参数：S A : Type*；h : Function.Surjective (algebraMap R T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.flip_mk_surjective`：TensorProduct.flip_mk_surjective (h : 
Function.Surjective (algebraMap R T)) : Function.Surjective ((TensorProduct.mk R
 S T).flip 1)
-/
lemma Algebra.TensorProduct.includeLeft_surjective
    (S A : Type*) [CommSemiring S] [Semiring A] [Algebra S A] [Algebra R A]
    [SMulCommClass R S A] (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective (includeLeft : A →ₐ[S] A ⊗[R] T) :=
  TensorProduct.flip_mk_surjective _ h

end

variable {R A B : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [NonUnitalNonAssocSemiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]

@[simp]
/-
**TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm** 是 Mathlib 中的一个定理，位于命名
空间 `TensorProduct.Algebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : NonUnitalNonAssocSemiring A]   [inst_2 : NonUnitalNonAssocSemiring B] [in
st_3 : _root_.Module R A] [inst_4 : _root_.Module R B]   [inst_5 : SMulCommClass
 R A A] [inst_6 : SMulCommClass R B B] [inst_7 : IsScalarTower R A A]   [inst_8 
: IsScalarTower R B B],   LinearMap.mul' R (TensorProduct R A B) ∘ₗ ↑(TensorProd
uct.tensorTensorTensorComm R A A B B) =     TensorProduct.map (LinearMap.mul' R 
A) (LinearMap.mul' R B)
参数：TensorProduct R A B；TensorProduct.tensorTensorTensorComm R A A B B；LinearMap.
mul' R A；LinearMap.mul' R B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.TensorProduct.sMulCommClass_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
· 使用定理 `Algebra.TensorProduct.isScalarTower_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm :
    LinearMap.mul' R (A ⊗[R] B) ∘ₗ tensorTensorTensorComm R A A B B =
      map (LinearMap.mul' R A) (LinearMap.mul' R B) := by
  ext
  simp
/-
**LinearMap.mul'_tensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : NonUnitalNonAssocSemiring A]   [inst_2 : NonUnitalNonAssocSemiring B] [in
st_3 : _root_.Module R A] [inst_4 : _root_.Module R B]   [inst_5 : SMulCommClass
 R A A] [inst_6 : SMulCommClass R B B] [inst_7 : IsScalarTower R A A]   [inst_8 
: IsScalarTower R B B],   LinearMap.mul' R (TensorProduct R A B) =     TensorPro
duct.map (LinearMap.mul' R A) (LinearMap.mul' R B) ∘ₗ ↑(TensorProduct.tensorTens
orTensorComm R A B A B)
参数：TensorProduct R A B；LinearMap.mul' R A；LinearMap.mul' R B；TensorProduct.tenso
rTensorTensorComm R A B A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext_fourfold'`：ext_fourfold' {φ ψ : M otimes[R] N otimes[R
] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, φ (w otimesₜ x otimesₜ (y o
timesₜ z)) = ψ (w…
· 使用定理 `Algebra.TensorProduct.sMulCommClass_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
· 使用定理 `Algebra.TensorProduct.isScalarTower_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma LinearMap.mul'_tensor :
    mul' R (A ⊗[R] B) = map (mul' R A) (mul' R B) ∘ₗ tensorTensorTensorComm R A B A B :=
  ext_fourfold' <| by simp
/-
**LinearMap.mulLeft_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.mulLeft_tmul (a : A) (b : B) : mulLeft R (a otimesₜ[R] b) = map 
(mulLeft R a) (mulLeft R b)
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.TensorProduct.sMulCommClass_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
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
lemma LinearMap.mulLeft_tmul (a : A) (b : B) :
    mulLeft R (a ⊗ₜ[R] b) = map (mulLeft R a) (mulLeft R b) := by
  ext; simp
/-
**LinearMap.mulRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.mulRight_tmul (a : A) (b : B) : mulRight R (a otimesₜ[R] b) = ma
p (mulRight R a) (mulRight R b)
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.TensorProduct.isScalarTower_right`：∀ {R : Type uR} {S : Type uS}
 {A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssoc
Semiring A]   [inst_2 : _root_.…
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
lemma LinearMap.mulRight_tmul (a : A) (b : B) :
    mulRight R (a ⊗ₜ[R] b) = map (mulRight R a) (mulRight R b) := by
  ext; simp

namespace TensorProduct
variable [StarRing R] [StarRing A] [StarRing B] [StarModule R A] [StarModule R B]

/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : StarMul (A ⊗[R] B) where
  star_mul x y :=
    x.induction_on (by simp) (fun _ _ ↦
      y.induction_on (by simp)
        fun _ _ ↦ by simp
      fun _ _ h₁ h₂ ↦ by simp [add_mul, mul_add, h₁, h₂])
    fun _ _ h₁ h₂ ↦ by simp [add_mul, mul_add, h₁, h₂]
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : StarRing (A ⊗[R] B) where
  star_add := by simp

end TensorProduct

namespace AlgHom

variable (R S A B : Type*)
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable [Algebra R S] [Algebra R B] [IsScalarTower R S B]

/-- Universal property of the base change of algebra.

An algebra map from the base change is equivalent to an algebra map over the base ring.

In categorical terms, this is an adjunction between:
1. `A ↦ S ⊗[R] A`, a functor `R-Alg ⥤ S-Alg` (the base change).
2. `B ↦ B`, a functor `S-Alg ⥤ R-Alg` (the restriction).
-/
/-
**AlgHom.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：liftEquiv : (A ->ₐ[R] B) ≃ (S otimes[R] A ->ₐ[S] B) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universal property of the base change of algebra.

An algebra map from the base change is equivalent to an algebra map over the bas
e ring.

In categorical terms, this is an adjunction between:
1. `A ↦ S ⊗[R] A`, a functor `R-Alg ⥤ S-Alg` (the base change).
2. `B ↦ B`, a functor `S-Alg ⥤ R-Alg` (the restriction).
-/
def liftEquiv : (A →ₐ[R] B) ≃ (S ⊗[R] A →ₐ[S] B) where
  toFun f :=
    .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y ↦ by
      rw [← LinearMap.mul_apply_apply S, ← LinearMap.compr₂_apply,
        ← LinearMap.mul_apply_apply S, ← LinearMap.compl₁₂_apply]
      congr; ext; simp
  invFun f := f.restrictScalars R |>.comp Algebra.TensorProduct.includeRight
  left_inv f := by ext; simp
  right_inv f := Algebra.TensorProduct.ext (Subsingleton.elim _ _) <| by ext; simp

variable {R S A B}
/-
**AlgHom.liftEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} {B : Type u_7} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring
 B] [inst_4 : Algebra R A] [inst_5 : Algebra S B] [inst_6 : Algebra R S]   [inst
_7 : Algebra R B] [inst_8 : IsScalarTower R S B] (f : A →ₐ[R] B) (s : S) (a : A)
,   ((AlgHom.liftEquiv R S A B) f) (s ⊗ₜ[R] a) = s • f a
参数：f : A →ₐ[R] B；s : S；a : A；(AlgHom.liftEquiv R S A B) f；s ⊗ₜ[R] a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma liftEquiv_tmul (f : A →ₐ[R] B) (s : S) (a : A) :
    f.liftEquiv R S A B (s ⊗ₜ a) = s • f a := rfl
/-
**AlgHom.liftEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} {B : Type u_7} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : Semiring A] [inst_3 : Semiring
 B] [inst_4 : Algebra R A] [inst_5 : Algebra S B] [inst_6 : Algebra R S]   [inst
_7 : Algebra R B] [inst_8 : IsScalarTower R S B] (f : TensorProduct R S A →ₐ[S] 
B) (a : A),   ((AlgHom.liftEquiv R S A B).symm f) a = f (1 ⊗ₜ[R] a)
参数：f : TensorProduct R S A →ₐ[S] B；a : A；(AlgHom.liftEquiv R S A B).symm f；1 ⊗ₜ[
R] a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma liftEquiv_symm_apply (f : S ⊗[R] A →ₐ[S] B) (a : A) :
    (liftEquiv ..).symm f a = f (1 ⊗ₜ[R] a) := rfl

@[ext high + 1]
/-
**AlgHom._root_.Algebra.TensorProduct.ext_ring** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.TensorProduct.ext_ring {f g : S ⊗[R] A →ₐ[S] B}
    (h : (AlgHom.restrictScalars R f).comp Algebra.TensorProduct.includeRight =
      (AlgHom.restrictScalars R g).comp Algebra.TensorProduct.includeRight) :
    f = g :=
  liftEquiv .. |>.symm.injective h

end AlgHom

