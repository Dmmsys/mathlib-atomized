/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Subalgebras in towers of algebras

In this file we prove facts about subalgebras in towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

## Main results

* `IsScalarTower.Subalgebra`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S/S₀` is a tower
* `IsScalarTower.Subalgebra'`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S₀/R` is a tower
* `Subalgebra.restrictScalars`: turn an `S`-subalgebra of `A` into an `R`-subalgebra of `A`,
  given that `A/S/R` is a tower

-/

@[expose] public section


open scoped Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {A}

/-
**Algebra.lmul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.ls
mul R R A x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x :=
  Eq.symm <| LinearMap.ext <| smul_def x

end Algebra

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A]
variable [Algebra R S] [Algebra S A]

/-
**IsScalarTower.subalgebra** 是 Mathlib 中的一个实例，位于命名空间 `IsScalarTower`。
形式化陈述：subalgebra (S₀ : Subalgebra R S) : IsScalarTower S₀ S A
参数：S₀ : Subalgebra R S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
-/
instance subalgebra (S₀ : Subalgebra R S) : IsScalarTower S₀ S A :=
  of_algebraMap_eq fun _ ↦ rfl

variable [Algebra R A] [IsScalarTower R S A]
/-
**IsScalarTower.subalgebra'** 是 Mathlib 中的一个实例，位于命名空间 `IsScalarTower`。
形式化陈述：subalgebra' (S₀ : Subalgebra R S) : IsScalarTower R S₀ A
参数：S₀ : Subalgebra R S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
-/
instance subalgebra' (S₀ : Subalgebra R S) : IsScalarTower R S₀ A :=
  @IsScalarTower.of_algebraMap_eq R S₀ A _ _ _ _ _ _ fun _ ↦
    (IsScalarTower.algebraMap_apply R S A _ :)

end Semiring

end IsScalarTower

namespace Subalgebra

open IsScalarTower

section Semiring

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A`, reinterpret
`U` as an `R`-subalgebra of `A`. -/
/-
**Subalgebra.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：restrictScalars (U : Subalgebra S A) : Subalgebra R A
参数：U : Subalgebra S A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A
`, reinterpret
`U` as an `R`-subalgebra of `A`.
-/
def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebraMap_mem' := fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R S A]
      exact U.algebraMap_mem _ }

@[simp]
/-
**Subalgebra.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_restrictScalars {U : Subalgebra S A} : (restrictScalars R U : Set A) =
 (U : Set A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars {U : Subalgebra S A} : (restrictScalars R U : Set A) = (U : Set A) :=
  rfl

@[simp]
/-
**Subalgebra.restrictScalars_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：restrictScalars_top : restrictScalars R (⊤ : Subalgebra S A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem restrictScalars_top : restrictScalars R (⊤ : Subalgebra S A) = ⊤ :=
  -- Porting note: `by dsimp` used to be `rfl`. This appears to work but causes
  -- this theorem to timeout in the kernel after minutes of thinking.
  SetLike.coe_injective <| by dsimp

@[simp]
/-
**Subalgebra.restrictScalars_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：restrictScalars_toSubmodule {U : Subalgebra S A} : Subalgebra.toSubmodule 
(U.restrictScalars R) = U.toSubmodule.restrictScalars R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem restrictScalars_toSubmodule {U : Subalgebra S A} :
    Subalgebra.toSubmodule (U.restrictScalars R) = U.toSubmodule.restrictScalars R :=
  SetLike.coe_injective rfl

@[simp]
/-
**Subalgebra.mem_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_restrictScalars {U : Subalgebra S A} {x : A} : x in restrictScalars R 
U ↔ x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_restrictScalars {U : Subalgebra S A} {x : A} : x ∈ restrictScalars R U ↔ x ∈ U :=
  Iff.rfl
/-
**Subalgebra.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : Subalg
ebra S A -> Subalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_restrictScalars`：mem_restrictScalars {U : Subalgebra S A}
 {x : A} : x in restrictScalars R U ↔ x in U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : Subalgebra S A → Subalgebra R A) := fun U V H ↦
  ext fun x ↦ by rw [← mem_restrictScalars R, H, mem_restrictScalars]

/-- Produces an `R`-algebra map from `U.restrictScalars R` given an `S`-algebra map from `U`.

This is a special case of `AlgHom.restrictScalars` that can be helpful in elaboration. -/
@[simp]
/-
**Subalgebra.ofRestrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：ofRestrictScalars (U : Subalgebra S A) (f : U ->ₐ[S] B) : U.restrictScalar
s R ->ₐ[R] B
参数：U : Subalgebra S A；f : U ->ₐ[S] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces an `R`-algebra map from `U.restrictScalars R` given an `S`-algebra map 
from `U`.

This is a special case of `AlgHom.restrictScalars` that can be helpful in elabor
ation.
-/
def ofRestrictScalars (U : Subalgebra S A) (f : U →ₐ[S] B) : U.restrictScalars R →ₐ[R] B :=
  f.restrictScalars R

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A)

@[simp]
/-
**Subalgebra.restrictScalars_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：restrictScalars_one : Submodule.restrictScalars R (1 : Submodule S A) = Su
balgebra.toSubmodule S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrictScalars_one :
    Submodule.restrictScalars R (1 : Submodule S A) = Subalgebra.toSubmodule S := by
  ext; simp
/-
**Subalgebra.codisjoint_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：codisjoint_one_iff (I : Ideal A) : Codisjoint (1 : Submodule S A) (I.restr
ictScalars S) ↔ Codisjoint (Subalgebra.toSubmodule S) (I.restrictScalars R)
参数：I : Ideal A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.codisjoint_restrictScalars_iff`：codisjoint_restrictScalars_iff
 {s t : Submodule R M} : Codisjoint (s.restrictScalars S) (t.restrictScalars S) 
↔ Codisjoint s t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.restrictScalars_one`：restrictScalars_one : Submodule.restrict
Scalars R (1 : Submodule S A) = Subalgebra.toSubmodule S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_one_iff (I : Ideal A) :
    Codisjoint (1 : Submodule S A) (I.restrictScalars S) ↔
      Codisjoint (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  simp [← Submodule.codisjoint_restrictScalars_iff R]
/-
**Subalgebra.disjoint_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：disjoint_one_iff (I : Ideal A) : Disjoint (1 : Submodule S A) (I.restrictS
calars S) ↔ Disjoint (Subalgebra.toSubmodule S) (I.restrictScalars R)
参数：I : Ideal A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.disjoint_restrictScalars_iff`：disjoint_restrictScalars_iff {s 
t : Submodule R M} : Disjoint (s.restrictScalars S) (t.restrictScalars S) ↔ Disj
oint s t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.restrictScalars_one`：restrictScalars_one : Submodule.restrict
Scalars R (1 : Submodule S A) = Subalgebra.toSubmodule S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_one_iff (I : Ideal A) :
    Disjoint (1 : Submodule S A) (I.restrictScalars S) ↔
      Disjoint (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  simp [← Submodule.disjoint_restrictScalars_iff R]

@[simp]
/-
**Subalgebra.range_isScalarTower_toAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`
。
形式化陈述：range_isScalarTower_toAlgHom : LinearMap.range (IsScalarTower.toAlgHom R S
 A : S ->ₗ[R] A) = Subalgebra.toSubmodule S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_isScalarTower_toAlgHom :
    LinearMap.range (IsScalarTower.toAlgHom R S A : S →ₗ[R] A) = Subalgebra.toSubmodule S := by
  ext
  simp [algebraMap_eq]

end CommSemiring

end Subalgebra

namespace IsScalarTower

open Subalgebra

variable [CommSemiring R] [CommSemiring S] [CommSemiring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-
**IsScalarTower.adjoin_range_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：adjoin_range_toAlgHom (t : Set A) : (Algebra.adjoin (toAlgHom R S A).range
 t).restrictScalars R = (Algebra.adjoin S t).restrictScalars R
参数：t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subalgebra.setRange_algebraMap`：setRange_algebraMap {R A : Type*} [CommS
emiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) : Set.range (alge
braMap S A) = (S : S…
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adjoin_range_toAlgHom (t : Set A) :
    (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R =
      (Algebra.adjoin S t).restrictScalars R :=
  Subalgebra.ext fun z ↦
    show z ∈ Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) ∪ t : Set A) ↔
         z ∈ Subsemiring.closure (Set.range (algebraMap S A) ∪ t : Set A) by simp

end IsScalarTower

