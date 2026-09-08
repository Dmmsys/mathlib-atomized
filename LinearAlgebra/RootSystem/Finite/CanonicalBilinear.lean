/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# The canonical bilinear form on a finite root pairing

Given a finite root pairing, we define a canonical map from weight space to coweight space, and the
corresponding bilinear form. This form is symmetric and Weyl-invariant, and if the base ring is
linearly ordered, then the form is root-positive, positive-semidefinite on the weight space, and
positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4. Thus, the pairings of roots and coroots in a crystallographic root pairing are
restricted to a small finite set of possibilities.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main definitions:
* `RootPairing.Polarization`: A distinguished linear map from the weight space to the coweight
  space.
* `RootPairing.RootForm` : The bilinear form on weight space corresponding to `Polarization`.

## Main results:
* `RootPairing.rootForm_self_sum_of_squares` : The inner product of any
  weight vector is a sum of squares.
* `RootPairing.rootForm_reflection_reflection_apply` : `RootForm` is invariant with respect
  to reflections.
* `RootPairing.rootForm_self_smul_coroot`: The inner product of a root with itself
  times the corresponding coroot is equal to two times Polarization applied to the root.
* `RootPairing.exists_ge_zero_eq_rootForm`: `RootForm` is positive semidefinite.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

-/

@[expose] public section

open Set Function
open Module hiding reflection
open Submodule (span)

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Fintype

variable [Fintype ι]

/-- An invariant linear map from weight space to coweight space. -/
/-
**RootPairing.Polarization** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：Polarization : M ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invariant linear map from weight space to coweight space.
-/
def Polarization : M →ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i

@[simp]
/-
**RootPairing.Polarization_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：Polarization_apply (x : M) : P.Polarization x = ∑ i, P.coroot' i x • P.cor
oot i
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Polarization_apply (x : M) :
    P.Polarization x = ∑ i, P.coroot' i x • P.coroot i := by
  simp [Polarization]

/-- An invariant linear map from coweight space to weight space. -/
/-
**RootPairing.CoPolarization** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：CoPolarization : N ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invariant linear map from coweight space to weight space.
-/
def CoPolarization : N →ₗ[R] M :=
  P.flip.Polarization

@[simp]
/-
**RootPairing.CoPolarization_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：CoPolarization_apply (x : N) : P.CoPolarization x = ∑ i, P.root' i x • P.r
oot i
参数：x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
-/
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.root' i x • P.root i :=
  P.flip.Polarization_apply x
/-
**RootPairing.CoPolarization_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：CoPolarization_eq : P.CoPolarization = P.flip.Polarization
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization :=
  rfl

/-- An invariant inner product on the weight space. -/
/-
**RootPairing.RootForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：RootForm : LinearMap.BilinForm R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invariant inner product on the weight space.
-/
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (P.coroot' i).smulRight (P.coroot' i)

/-- An invariant inner product on the coweight space. -/
/-
**RootPairing.CorootForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：CorootForm : LinearMap.BilinForm R N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invariant inner product on the coweight space.
-/
def CorootForm : LinearMap.BilinForm R N :=
  P.flip.RootForm
/-
**RootPairing.rootForm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_apply_apply (x y : M) : P.RootForm x y = ∑ i, P.coroot' i x * P.c
oroot' i y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ i, P.coroot' i x * P.coroot' i y := by
  simp [RootForm]
/-
**RootPairing.corootForm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：corootForm_apply_apply (x y : N) : P.CorootForm x y = ∑ i, P.root' i x * P
.root' i y
参数：x y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
-/
lemma corootForm_apply_apply (x y : N) : P.CorootForm x y =
    ∑ i, P.root' i x * P.root' i y :=
  P.flip.rootForm_apply_apply x y
/-
**RootPairing.toLinearMap_apply_apply_Polarization** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：toLinearMap_apply_apply_Polarization (x y : M) : P.toLinearMap y (P.Polari
zation x) = P.RootForm x y
参数：x y : M。
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
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toLinearMap_apply_apply_Polarization (x y : M) :
    P.toLinearMap y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]
/-
**RootPairing.toLinearMap_apply_CoPolarization** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：toLinearMap_apply_CoPolarization (x : N) : P.toLinearMap (P.CoPolarization
 x) = P.CorootForm x
参数：x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.toLinearMap_apply_apply_Polarization`：toLinearMap_apply_appl
y_Polarization (x y : M) : P.toLinearMap y (P.Polarization x) = P.RootForm x y
-/
lemma toLinearMap_apply_CoPolarization (x : N) :
    P.toLinearMap (P.CoPolarization x) = P.CorootForm x := by
  ext y
  exact P.flip.toLinearMap_apply_apply_Polarization x y
/-
**RootPairing.flip_comp_polarization_eq_rootForm** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：flip_comp_polarization_eq_rootForm : P.flip.toLinearMap ∘ₗ P.Polarization 
= P.RootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma flip_comp_polarization_eq_rootForm :
    P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm := by
  ext; simp [rootForm_apply_apply, RootPairing.flip]
/-
**RootPairing.self_comp_coPolarization_eq_corootForm** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：self_comp_coPolarization_eq_corootForm : P.toLinearMap ∘ₗ P.CoPolarization
 = P.CorootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.flip_comp_polarization_eq_rootForm`：flip_comp_polarization_e
q_rootForm : P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm
-/
lemma self_comp_coPolarization_eq_corootForm :
    P.toLinearMap ∘ₗ P.CoPolarization = P.CorootForm :=
  P.flip.flip_comp_polarization_eq_rootForm
/-
**RootPairing.polarization_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing`。
形式化陈述：polarization_apply_eq_zero_iff (m : M) : P.Polarization m = 0 ↔ P.RootForm
 m = 0
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.flip_comp_polarization_eq_rootForm`：flip_comp_polarization_e
q_rootForm : P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `RootPairing.flip_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Type 
u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _r
oot_.Module R M] […
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
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma polarization_apply_eq_zero_iff (m : M) :
    P.Polarization m = 0 ↔ P.RootForm m = 0 := by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h ↦ by simp [h], ?_⟩
  rintro (h : P.flip.toPerfPair (P.Polarization m) = 0)
  simpa only [EmbeddingLike.map_eq_zero_iff] using h
/-
**RootPairing.coPolarization_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：coPolarization_apply_eq_zero_iff (n : N) : P.CoPolarization n = 0 ↔ P.Coro
otForm n = 0
参数：n : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.polarization_apply_eq_zero_iff`：polarization_apply_eq_zero_i
ff (m : M) : P.Polarization m = 0 ↔ P.RootForm m = 0
-/
lemma coPolarization_apply_eq_zero_iff (n : N) :
    P.CoPolarization n = 0 ↔ P.CorootForm n = 0 :=
  P.flip.polarization_apply_eq_zero_iff n
/-
**RootPairing.ker_polarization_eq_ker_rootForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：ker_polarization_eq_ker_rootForm : LinearMap.ker P.Polarization = LinearMa
p.ker P.RootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.polarization_apply_eq_zero_iff`：polarization_apply_eq_zero_i
ff (m : M) : P.Polarization m = 0 ↔ P.RootForm m = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_polarization_eq_ker_rootForm :
    LinearMap.ker P.Polarization = LinearMap.ker P.RootForm := by
  ext; simp only [LinearMap.mem_ker, P.polarization_apply_eq_zero_iff]
/-
**RootPairing.ker_copolarization_eq_ker_corootForm** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：ker_copolarization_eq_ker_corootForm : LinearMap.ker P.CoPolarization = Li
nearMap.ker P.CorootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.ker_polarization_eq_ker_rootForm`：ker_polarization_eq_ker_ro
otForm : LinearMap.ker P.Polarization = LinearMap.ker P.RootForm
-/
lemma ker_copolarization_eq_ker_corootForm :
    LinearMap.ker P.CoPolarization = LinearMap.ker P.CorootForm :=
  P.flip.ker_polarization_eq_ker_rootForm
/-
**RootPairing.rootForm_symmetric** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_symmetric : LinearMap.IsSymm P.RootForm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma rootForm_symmetric :
    LinearMap.IsSymm P.RootForm := by
  simp [LinearMap.isSymm_def, mul_comm, rootForm_apply_apply]

@[simp]
/-
**RootPairing.rootForm_reflection_reflection_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：rootForm_reflection_reflection_apply (i : ι) (x y : M) : P.RootForm (P.ref
lection i x) (P.reflection i y) = P.RootForm x y
参数：i : ι；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RootPairing.coroot'_reflection`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflectionPerm i)
    (fun j ↦ (P.coroot' (P.reflectionPerm i j) x) * (P.coroot' (P.reflectionPerm i j) y))
    (fun j ↦ P.coroot' j x * P.coroot' j y) (congrFun rfl)
/-
**RootPairing.rootForm_self_sum_of_squares** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：rootForm_self_sum_of_squares (x : M) : IsSumSq (P.RootForm x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.sum_mul_self`：IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι 
: Type*} (I : Finset ι) (a : ι -> R) : IsSumSq (∑ i in I, a i * a i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
-/
lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ IsSumSq.sum_mul_self Finset.univ _
/-
**RootPairing.rootForm_root_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_root_self (j : ι) : P.RootForm (P.root j) (P.root j) = ∑ (i : ι),
 (P.pairing j i) * (P.pairing j i)
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]
/-
**RootPairing.range_polarization_domRestrict_le_span_coroot** 是 Mathlib 中的一个定理，位
于命名空间 `RootPairing`。
形式化陈述：range_polarization_domRestrict_le_span_coroot : LinearMap.range (P.Polariz
ation.domRestrict (P.rootSpan R)) <= P.corootSpan R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.domRestrict_apply`：domRestrict_apply (f : M ->ₛₗ[σ₁₂] M₂) (p :
 Submodule R M) (x : p) : f.domRestrict p x = f x
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) ≤ P.corootSpan R := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, LinearMap.domRestrict_apply, Polarization_apply]
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => P.toLinearMap x (P.coroot i)
  simp
/-
**RootPairing.corootSpan_dualAnnihilator_le_ker_rootForm** 是 Mathlib 中的一个定理，位于命名
空间 `RootPairing`。
形式化陈述：corootSpan_dualAnnihilator_le_ker_rootForm : (P.corootSpan R).dualAnnihila
tor.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) <= P.RootForm.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'`：corootSp
an_dualAnnihilator_map_eq_iInf_ker_coroot' : (P.corootSpan R).dualAnnihilator.ma
p (P.toPerfPair.symm : Dual R N ->ₗ[R] M) = ⨅ i, (P.…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem corootSpan_dualAnnihilator_le_ker_rootForm :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N →ₗ[R] M) ≤
      P.RootForm.ker := by
  rw [P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  intro x hx
  ext y
  simp_all [coroot', rootForm_apply_apply]
/-
**RootPairing.rootSpan_dualAnnihilator_le_ker_rootForm** 是 Mathlib 中的一个定理，位于命名空间
 `RootPairing`。
形式化陈述：rootSpan_dualAnnihilator_le_ker_rootForm : (P.rootSpan R).dualAnnihilator.
map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) <= P.CorootForm.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.corootSpan_dualAnnihilator_le_ker_rootForm`：corootSpan_dualA
nnihilator_le_ker_rootForm : (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.
symm : Dual R N ->ₗ[R] M) <= P.RootForm.ker
-/
theorem rootSpan_dualAnnihilator_le_ker_rootForm :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M →ₗ[R] N) ≤
      P.CorootForm.ker :=
  P.flip.corootSpan_dualAnnihilator_le_ker_rootForm

end Fintype

section IsValuedIn

variable (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [Module S N] [IsScalarTower S R N] [P.IsValuedIn S] [Fintype ι] {i j : ι}

/-- Polarization restricted to `S`-span of roots. -/
/-
**RootPairing.PolarizationIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：PolarizationIn : P.rootSpan S ->ₗ[S] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Polarization restricted to `S`-span of roots.
-/
def PolarizationIn : P.rootSpan S →ₗ[S] N :=
  ∑ i : ι, LinearMap.toSpanSingleton S N (P.coroot i) ∘ₗ P.coroot'In S i

omit [IsScalarTower S R N] in
/-
**RootPairing.PolarizationIn_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：PolarizationIn_apply (x : P.rootSpan S) : P.PolarizationIn S x = ∑ i, P.co
root'In S i x • P.coroot i
参数：x : P.rootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma PolarizationIn_apply (x : P.rootSpan S) :
    P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i := by
  simp [PolarizationIn]
/-
**RootPairing.PolarizationIn_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：PolarizationIn_eq (x : P.rootSpan S) : P.PolarizationIn S x = P.Polarizati
on x
参数：x : P.rootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `algebra_compatible_smul`：algebra_compatible_smul (r : R) (m : M) : r • m
 = (algebraMap R A) r • m
· 使用定理 `RootPairing.algebraMap_coroot'In_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
-/
lemma PolarizationIn_eq (x : P.rootSpan S) :
    P.PolarizationIn S x = P.Polarization x := by
  simp only [PolarizationIn, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, comp_apply,
    LinearMap.toSpanSingleton_apply, Polarization_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [algebra_compatible_smul R (P.coroot'In S i x) (P.coroot i), algebraMap_coroot'In_apply]
/-
**RootPairing.range_polarizationIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：range_polarizationIn : Submodule.map P.Polarization (P.rootSpan R) = Linea
rMap.range (P.PolarizationIn R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `RootPairing.instIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_
4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _roo
t_.Module R M] […
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
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用引理 `RootPairing.PolarizationIn_eq`：PolarizationIn_eq (x : P.rootSpan S) : P.
PolarizationIn S x = P.Polarization x
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_polarizationIn :
    Submodule.map P.Polarization (P.rootSpan R) = LinearMap.range (P.PolarizationIn R) := by
  ext x
  simp [PolarizationIn_eq]

/-- Polarization restricted to `S`-span of roots. -/
/-
**RootPairing.CoPolarizationIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：CoPolarizationIn : P.corootSpan S ->ₗ[S] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […

--- 原说明 ---
Polarization restricted to `S`-span of roots.
-/
def CoPolarizationIn : P.corootSpan S →ₗ[S] M :=
  P.flip.PolarizationIn S

omit [IsScalarTower S R M] in
/-
**RootPairing.CoPolarizationIn_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：CoPolarizationIn_apply (x : P.corootSpan S) : P.CoPolarizationIn S x = ∑ i
, P.root'In S i x • P.root i
参数：x : P.corootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.PolarizationIn_apply`：PolarizationIn_apply (x : P.rootSpan S
) : P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma CoPolarizationIn_apply (x : P.corootSpan S) :
    P.CoPolarizationIn S x = ∑ i, P.root'In S i x • P.root i :=
  P.flip.PolarizationIn_apply S x
/-
**RootPairing.CoPolarizationIn_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：CoPolarizationIn_eq (x : P.corootSpan S) : P.CoPolarizationIn S x = P.CoPo
larization x
参数：x : P.corootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.PolarizationIn_eq`：PolarizationIn_eq (x : P.rootSpan S) : P.
PolarizationIn S x = P.Polarization x
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma CoPolarizationIn_eq (x : P.corootSpan S) :
    P.CoPolarizationIn S x = P.CoPolarization x :=
  P.flip.PolarizationIn_eq S x

/-- A canonical bilinear form on the span of roots in a finite root pairing, taking values in a
commutative ring, where the root-coroot pairing takes values in that ring. -/
/-
**RootPairing.RootFormIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：RootFormIn : LinearMap.BilinForm S (P.rootSpan S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A canonical bilinear form on the span of roots in a finite root pairing, taking 
values in a
commutative ring, where the root-coroot pairing takes values in that ring.
-/
def RootFormIn : LinearMap.BilinForm S (P.rootSpan S) :=
  ∑ i, (P.coroot'In S i).smulRight (P.coroot'In S i)

omit [Module S N] [IsScalarTower S R N] in
/-
**RootPairing.rootFormIn_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootFormIn_isSymm : (P.RootFormIn S).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma rootFormIn_isSymm :
    (P.RootFormIn S).IsSymm := by
  simp [LinearMap.isSymm_def, mul_comm, RootFormIn]

omit [Module S N] [IsScalarTower S R N] in
@[simp]
/-
**RootPairing.algebraMap_rootFormIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：algebraMap_rootFormIn (x y : P.rootSpan S) : (algebraMap S R) (P.RootFormI
n S x y) = P.RootForm x y
参数：x y : P.rootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RootPairing.algebraMap_coroot'In_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_rootFormIn (x y : P.rootSpan S) :
    (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y := by
  simp [RootFormIn, rootForm_apply_apply]
/-
**RootPairing.toLinearMap_apply_PolarizationIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：toLinearMap_apply_PolarizationIn (x y : P.rootSpan S) : P.toLinearMap y (P
.PolarizationIn S x) = (algebraMap S R) (P.RootFormIn S x y)
参数：x y : P.rootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.PolarizationIn_eq`：PolarizationIn_eq (x : P.rootSpan S) : P.
PolarizationIn S x = P.Polarization x
· 使用引理 `RootPairing.algebraMap_rootFormIn`：algebraMap_rootFormIn (x y : P.rootSp
an S) : (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y
· 使用引理 `RootPairing.toLinearMap_apply_apply_Polarization`：toLinearMap_apply_appl
y_Polarization (x y : M) : P.toLinearMap y (P.Polarization x) = P.RootForm x y
-/
lemma toLinearMap_apply_PolarizationIn (x y : P.rootSpan S) :
    P.toLinearMap y (P.PolarizationIn S x) =
      (algebraMap S R) (P.RootFormIn S x y) := by
  rw [PolarizationIn_eq, algebraMap_rootFormIn]
  exact toLinearMap_apply_apply_Polarization P x y

omit [IsScalarTower S R N] in
/-
**RootPairing.range_polarizationIn_le_span_coroot** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：range_polarizationIn_le_span_coroot : LinearMap.range (P.PolarizationIn S)
 <= P.corootSpan S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.PolarizationIn_apply`：PolarizationIn_apply (x : P.rootSpan S
) : P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i
-/
lemma range_polarizationIn_le_span_coroot :
    LinearMap.range (P.PolarizationIn S) ≤ P.corootSpan S := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [PolarizationIn_apply] at hy
  exact (Submodule.mem_span_range_iff_exists_fun S).mpr
    (Exists.intro (fun i ↦ (P.coroot'In S i) y) hy)

/-- A version of SGA3 XXI Lemma 1.2.1 (10), adapted to change of rings. -/
/-
**RootPairing.rootFormIn_self_smul_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
`。
形式化陈述：rootFormIn_self_smul_coroot (i : ι) : P.RootFormIn S (P.rootSpanMem S i) (
P.rootSpanMem S i) • P.coroot i = 2 • P.PolarizationIn S (P.rootSpanMem S i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.PolarizationIn_apply`：PolarizationIn_apply (x : P.rootSpan S
) : P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.pairingIn_reflectionPerm`：pairingIn_reflectionPerm [Faithful
SMul S R] [P.IsValuedIn S] (i j k : ι) : P.pairingIn S j (P.reflectionPerm i k) 
= P.pairingIn S (P.reflect…
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_left`：pairingIn_reflectionPerm
_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S (P.refl
ectionPerm i i) j = - P.pairingIn S …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `RootPairing.RootFormIn.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
A version of SGA3 XXI Lemma 1.2.1 (10), adapted to change of rings.
-/
lemma rootFormIn_self_smul_coroot (i : ι) :
    P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i) • P.coroot i =
      2 • P.PolarizationIn S (P.rootSpanMem S i) := by
  have hP : P.PolarizationIn S (P.rootSpanMem S i) =
      ∑ j : ι, P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j) := by
    simp_rw [PolarizationIn_apply, coroot'In_rootSpanMem_eq_pairingIn]
    exact (Fintype.sum_equiv (P.reflectionPerm i)
          (fun j ↦ P.pairingIn S i (P.reflectionPerm i j) • P.coroot (P.reflectionPerm i j))
          (fun j ↦ P.pairingIn S i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [PolarizationIn_apply]
  simp only [coroot'In_rootSpanMem_eq_pairingIn, pairingIn_reflectionPerm,
    pairingIn_reflectionPerm_self_left, ← reflectionPerm_coroot, neg_smul,
    smul_sub, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add, RootFormIn]
  simp only [LinearMap.coe_sum, LinearMap.coe_smulRight, Finset.sum_apply,
    coroot'In_rootSpanMem_eq_pairingIn, LinearMap.smul_apply, smul_eq_mul, Finset.sum_smul,
    root_coroot_eq_pairing, Finset.sum_neg_distrib, add_neg_cancel, sub_eq_zero]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← P.algebraMap_pairingIn S, IsScalarTower.algebraMap_smul, ← mul_smul]
/-
**RootPairing.prod_rootFormIn_smul_coroot_mem_range_PolarizationIn** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing`。
形式化陈述：prod_rootFormIn_smul_coroot_mem_range_PolarizationIn (i : ι) : (∏ j : ι, P
.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j)) • P.coroot i in LinearMap
.range (P.PolarizationIn S)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `RootPairing.rootFormIn_self_smul_coroot`：rootFormIn_self_smul_coroot (i 
: ι) : P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i) • P.coroot i = 2 •
 P.PolarizationIn S (P.rootSp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma prod_rootFormIn_smul_coroot_mem_range_PolarizationIn (i : ι) :
    (∏ j : ι, P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j)) • P.coroot i ∈
      LinearMap.range (P.PolarizationIn S) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun j ↦ P.RootFormIn S (P.rootSpanMem S j) (P.rootSpanMem S j))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootFormIn_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use c • 2 • (P.rootSpanMem S i)
  rw [map_smul, two_smul, two_smul, map_add]

end IsValuedIn

section MoreFintype

variable [Fintype ι]

/-- A version of SGA3 XXI Lemma 1.2.1 (10). -/
/-
**RootPairing.rootForm_self_smul_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_self_smul_coroot (i : ι) : (P.RootForm (P.root i) (P.root i)) • P
.coroot i = 2 • P.Polarization (P.root i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `RootPairing.instIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_
4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _roo
t_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_self_apply`：algebraMap_self_apply (x : R) : algebraMa
p R R x = x
· 使用引理 `RootPairing.rootFormIn_self_smul_coroot`：rootFormIn_self_smul_coroot (i 
: ι) : P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i) • P.coroot i = 2 •
 P.PolarizationIn S (P.rootSp…
· 使用引理 `RootPairing.PolarizationIn_eq`：PolarizationIn_eq (x : P.rootSpan S) : P.
PolarizationIn S x = P.Polarization x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_rootFormIn`：algebraMap_rootFormIn (x y : P.rootSp
an S) : (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y

--- 原说明 ---
A version of SGA3 XXI Lemma 1.2.1 (10).
-/
lemma rootForm_self_smul_coroot (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have : (algebraMap R R) ((P.RootFormIn R) (P.rootSpanMem R i) (P.rootSpanMem R i)) • P.coroot i =
      2 • P.Polarization (P.root i) := by
    rw [Algebra.algebraMap_self_apply, P.rootFormIn_self_smul_coroot R i, PolarizationIn_eq]
  rw [← this, algebraMap_rootFormIn]
/-
**RootPairing.corootForm_self_smul_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：corootForm_self_smul_root (i : ι) : (P.CorootForm (P.coroot i) (P.coroot i
)) • P.root i = 2 • P.CoPolarization (P.coroot i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
-/
lemma corootForm_self_smul_root (i : ι) :
    (P.CorootForm (P.coroot i) (P.coroot i)) • P.root i = 2 • P.CoPolarization (P.coroot i) :=
  rootForm_self_smul_coroot (P.flip) i
/-
**RootPairing.four_nsmul_coPolarization_compl_polarization_apply_root** 是 Mathli
b 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：four_nsmul_coPolarization_compl_polarization_apply_root (i : ι) : (4 • P.C
oPolarization ∘ₗ P.Polarization) (P.root i) = (P.RootForm (P.root i) (P.root i) 
* P.CorootForm (P.coroot i) (P.coroot i)) • P.root i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `RootPairing.corootForm_self_smul_root`：corootForm_self_smul_root (i : ι)
 : (P.CorootForm (P.coroot i) (P.coroot i)) • P.root i = 2 • P.CoPolarization (P
.coroot i)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma four_nsmul_coPolarization_compl_polarization_apply_root (i : ι) :
    (4 • P.CoPolarization ∘ₗ P.Polarization) (P.root i) =
    (P.RootForm (P.root i) (P.root i) * P.CorootForm (P.coroot i) (P.coroot i)) • P.root i := by
  rw [LinearMap.smul_apply, LinearMap.comp_apply, show 4 = 2 * 2 from rfl, mul_smul, ← map_nsmul,
    ← rootForm_self_smul_coroot, map_smul, smul_comm, ← corootForm_self_smul_root, smul_smul]
/-
**RootPairing.four_smul_rootForm_sq_eq_coxeterWeight_smul** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing`。
形式化陈述：four_smul_rootForm_sq_eq_coxeterWeight_smul (i j : ι) : 4 • (P.RootForm (P
.root i) (P.root j)) ^ 2 = P.coxeterWeight i j • (P.RootForm (P.root i) (P.root 
i) * P.RootForm (P.root j) (P.root j))
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.toLinearMap_apply_apply_Polarization`：toLinearMap_apply_appl
y_Polarization (x y : M) : P.toLinearMap y (P.Polarization x) = P.RootForm x y
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `RootPairing.pairing.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3}
 {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_
.Module R M] […
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `RootPairing.coxeterWeight.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 35 条，此处仅展示前 30 条）
-/
lemma four_smul_rootForm_sq_eq_coxeterWeight_smul (i j : ι) :
    4 • (P.RootForm (P.root i) (P.root j)) ^ 2 = P.coxeterWeight i j •
      (P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j)) := by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toLinearMap (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toLinearMap_apply_apply_Polarization, LinearMap.map_smul_of_tower, ← smul_assoc,
      Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.root j) =
      P.toLinearMap (P.root i) (2 • P.Polarization (P.root j)) := by
    rw [show (P.RootForm (P.root i)) (P.root j) = (P.RootForm (P.root j)) (P.root i) by
      apply (rootForm_symmetric P).eq, ← toLinearMap_apply_apply_Polarization,
      LinearMap.map_smul_of_tower]
  rw [sq, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul, hij, ← rootForm_self_smul_coroot,
    smul_mul_assoc 2, ← mul_smul_comm, hji, ← rootForm_self_smul_coroot, map_smul, ← pairing,
    map_smul, ← pairing, smul_eq_mul, smul_eq_mul, smul_eq_mul, coxeterWeight]
  ring
/-
**RootPairing.prod_rootForm_smul_coroot_mem_range_domRestrict** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing`。
形式化陈述：prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) : (∏ a : ι, P.Root
Form (P.root a) (P.root a)) • P.coroot i in LinearMap.range (P.Polarization.domR
estrict (P.rootSpan R))
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `Submodule.mem_span_of_mem`：mem_span_of_mem {s : Set M} {x : M} (hx : x i
n s) : x in span R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈
      LinearMap.range (P.Polarization.domRestrict (P.rootSpan R)) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨c • 2 • P.root i, by aesop⟩
  simp

end MoreFintype

section IsValuedInOrdered

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  [Algebra S R] [FaithfulSMul S R] [Module S M]
  [IsScalarTower S R M] [P.IsValuedIn S] [Fintype ι] {i j : ι}

/-- The bilinear form of a finite root pairing taking values in a linearly-ordered ring, as a
root-positive form. -/
/-
**RootPairing.posRootForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：posRootForm : P.RootPositiveForm S where form
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y

--- 原说明 ---
The bilinear form of a finite root pairing taking values in a linearly-ordered r
ing, as a
root-positive form.
-/
def posRootForm : P.RootPositiveForm S where
  form := P.RootForm
  symm := P.rootForm_symmetric
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
  exists_eq i j := ⟨∑ k, P.pairingIn S i k * P.pairingIn S j k, by simp [rootForm_apply_apply]⟩
  exists_pos_eq i := by
    refine ⟨∑ k, P.pairingIn S i k ^ 2, ?_, by simp [sq, rootForm_apply_apply]⟩
    exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _) ⟨i, by simp⟩
/-
**RootPairing.algebraMap_posRootForm_posForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing`。
形式化陈述：algebraMap_posRootForm_posForm (x y : span S (range P.root)) : (algebraMap
 S R) ((P.posRootForm S).posForm x y) = P.RootForm x y
参数：x y : span S (range P.root)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_posRootForm_posForm (x y : span S (range P.root)) :
    (algebraMap S R) ((P.posRootForm S).posForm x y) = P.RootForm x y := by
  simp [posRootForm]

@[simp]
/-
**RootPairing.posRootForm_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：posRootForm_eq : (P.posRootForm S).posForm = P.RootFormIn S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_posRootForm_posForm`：algebraMap_posRootForm_posFo
rm (x y : span S (range P.root)) : (algebraMap S R) ((P.posRootForm S).posForm x
 y) = P.RootForm x y
· 使用引理 `RootPairing.algebraMap_rootFormIn`：algebraMap_rootFormIn (x y : P.rootSp
an S) : (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posRootForm_eq :
    (P.posRootForm S).posForm = P.RootFormIn S := by
  ext
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_posRootForm_posForm, algebraMap_rootFormIn]
/-
**RootPairing.exists_ge_zero_eq_rootForm** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
形式化陈述：exists_ge_zero_eq_rootForm (x : M) (hx : x in span S (range P.root)) : exi
sts s >= 0, algebraMap S R s = P.RootForm x x
参数：x : M；hx : x in span S (range P.root)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.nonneg`：IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] 
[IsStrictOrderedRing R] [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 <= s
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsSumSq.sum_mul_self`：IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι 
: Type*} (I : Finset ι) (a : ι -> R) : IsSumSq (∑ i in I, a i * a i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.coroot'_apply_apply_mem_of_mem_span`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem exists_ge_zero_eq_rootForm (x : M) (hx : x ∈ span S (range P.root)) :
    ∃ s ≥ 0, algebraMap S R s = P.RootForm x x := by
  refine ⟨(P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩, IsSumSq.nonneg ?_, by simp [posRootForm]⟩
  choose s hs using P.coroot'_apply_apply_mem_of_mem_span S hx
  suffices (P.posRootForm S).posForm ⟨x, hx⟩ ⟨x, hx⟩ = ∑ i, s i * s i from
    this ▸ IsSumSq.sum_mul_self Finset.univ s
  apply FaithfulSMul.algebraMap_injective S R
  simp only [posRootForm, RootPositiveForm.algebraMap_posForm, map_sum, map_mul]
  simp [hs, rootForm_apply_apply]
/-
**RootPairing.posRootForm_posForm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：posRootForm_posForm_apply_apply (x y : P.rootSpan S) : (P.posRootForm S).p
osForm x y = ∑ i, P.coroot'In S i x * P.coroot'In S i y
参数：x y : P.rootSpan S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_posForm`：∀ {ι : Type u_1} {R : T
ype u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [ins
t_1 : LinearOrder S] [inst_2 : CommRi…
· 使用引理 `RootPairing.rootForm_apply_apply`：rootForm_apply_apply (x y : M) : P.Roo
tForm x y = ∑ i, P.coroot' i x * P.coroot' i y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RootPairing.algebraMap_coroot'In_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posRootForm_posForm_apply_apply (x y : P.rootSpan S) : (P.posRootForm S).posForm x y =
    ∑ i, P.coroot'In S i x * P.coroot'In S i y := by
  refine (FaithfulSMul.algebraMap_injective S R) ?_
  simp [posRootForm, rootForm_apply_apply]
/-
**RootPairing.zero_le_posForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_le_posForm (x : span S (range P.root)) : 0 <= (P.posRootForm S).posFo
rm x x
参数：x : span S (range P.root)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.exists_ge_zero_eq_rootForm`：exists_ge_zero_eq_rootForm (x : 
M) (hx : x in span S (range P.root)) : exists s >= 0, algebraMap S R s = P.RootF
orm x x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_posRootForm_posForm`：algebraMap_posRootForm_posFo
rm (x y : span S (range P.root)) : (algebraMap S R) ((P.posRootForm S).posForm x
 y) = P.RootForm x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma zero_le_posForm (x : span S (range P.root)) :
    0 ≤ (P.posRootForm S).posForm x x := by
  obtain ⟨s, _, hs⟩ := P.exists_ge_zero_eq_rootForm S x.1 x.2
  have : s = (P.posRootForm S).posForm x x :=
    FaithfulSMul.algebraMap_injective S R <| (P.algebraMap_posRootForm_posForm S x x) ▸ hs
  rwa [← this]

omit [Fintype ι]
variable [Finite ι]
/-
**RootPairing.zero_lt_pairingIn_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_lt_pairingIn_iff' : 0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.zero_lt_pairingIn_iff`：zero_lt_pairingIn_iff [IsStrictOrdere
dRing S] : 0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i
-/
lemma zero_lt_pairingIn_iff' :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i :=
  let _i : Fintype ι := Fintype.ofFinite ι
  zero_lt_pairingIn_iff (P.posRootForm S) i j
/-
**RootPairing.pairingIn_lt_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_lt_zero_iff : P.pairingIn S i j < 0 ↔ P.pairingIn S j i < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_left`：pairingIn_reflectionPerm
_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S (P.refl
ectionPerm i i) j = - P.pairingIn S …
· 使用引理 `RootPairing.zero_lt_pairingIn_iff'`：zero_lt_pairingIn_iff' : 0 < P.pairi
ngIn S i j ↔ 0 < P.pairingIn S j i
-/
lemma pairingIn_lt_zero_iff :
    P.pairingIn S i j < 0 ↔ P.pairingIn S j i < 0 := by
  simpa using P.zero_lt_pairingIn_iff' S (i := i) (j := P.reflectionPerm j j)
/-
**RootPairing.pairingIn_le_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_le_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree 
R M] : P.pairingIn S i j <= 0 ↔ P.pairingIn S j i <= 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.pairingIn_eq_zero_iff`：pairingIn_eq_zero_iff {S : Type*} [Co
mmRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] [IsDomain R] [Module
.IsTorsionFree R M] [Ne…
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用引理 `RootPairing.pairingIn_lt_zero_iff`：pairingIn_lt_zero_iff : P.pairingIn S
 i j < 0 ↔ P.pairingIn S j i < 0
-/
lemma pairingIn_le_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.pairingIn S i j ≤ 0 ↔ P.pairingIn S j i ≤ 0 := by
  rcases eq_or_ne (P.pairingIn S i j) 0 with hij | hij <;>
  rcases eq_or_ne (P.pairingIn S j i) 0 with hji | hji
  · rw [hij, hji]
  · rw [hij, P.pairingIn_eq_zero_iff.mp hij]
  · rw [hji, P.pairingIn_eq_zero_iff.mp hji]
  · rw [le_iff_eq_or_lt, le_iff_eq_or_lt, or_iff_right hij, or_iff_right hji]
    exact P.pairingIn_lt_zero_iff S

end IsValuedInOrdered

end RootPairing

