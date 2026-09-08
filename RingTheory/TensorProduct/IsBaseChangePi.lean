/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change properties

This file proves that several constructions in linear algebra
commute with base change, as expressed by `IsBaseChange`.

* `IsBaseChange.prodMap`, `IsBaseChange.pi`: binary and finite products.

In particular, localization of modules commutes with binary and finite products.

* `IsBaseChange.directSum`: base change for direct sums

* Homomorphism modules

-/

public section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace IsBaseChange

open TensorProduct

/-- Base change commutes with binary products. -/
/-
**IsBaseChange.prodMap** 是 Mathlib 中的一个引理，位于命名空间 `IsBaseChange`。
形式化陈述：prodMap {M N M' N' : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R 
M] [Module R N] [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'
] [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N'] (f :
 M ->ₗ[R] M') (g : N ->ₗ[R] N') (hf : IsBaseChange S f) (hg : IsBaseChange S g) 
: IsBaseChange S (f.prodMap g)
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] N'；hf : IsBaseChange S f；hg : IsBaseChange S g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Base change commutes with binary products.
-/
lemma prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (f.prodMap g) := by
  apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
  intro p
  simp [equiv_tmul]

/-- Base change commutes with finite products. -/
/-
**IsBaseChange.pi** 是 Mathlib 中的一个引理，位于命名空间 `IsBaseChange`。
形式化陈述：pi {ι : Type*} [Finite ι] {M M' : ι -> Type*} [forall i, AddCommMonoid (M 
i)] [forall i, AddCommMonoid (M' i)] [forall i, Module R (M i)] [forall i, Modul
e R (M' i)] [forall i, Module S (M' i)] [forall i, IsScalarTower R S (M' i)] (f 
: forall i, M i ->ₗ[R] M' i) (hf : forall i, IsBaseChange S (f i)) : IsBaseChang
e S (.pi fun i => f i ∘ₗ .proj i)
参数：M i；M' i；M i；M' i；M' i；M' i；f : forall i, M i ->ₗ[R] M' i；hf : forall i, IsBa
seChange S (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TensorProduct.piRight_apply`：piRight_apply (x : N otimes[R] (forall i, M
 i)) : piRight R S N M x = piRightHom R S N M x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Base change commutes with finite products.
-/
lemma pi {ι : Type*} [Finite ι]
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)] [∀ i, Module S (M' i)]
    [∀ i, IsScalarTower R S (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) (hf : ∀ i, IsBaseChange S (f i)) :
    IsBaseChange S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  classical
  cases nonempty_fintype ι
  apply of_equiv <| piRight R S _ M ≪≫ₗ .piCongrRight fun i ↦ (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]
/-
**IsBaseChange.finitePow** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：finitePow (ι : Type*) [Finite ι] {M M' : Type*} [AddCommMonoid M] [AddComm
Monoid M'] [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M'] {f : 
M ->ₗ[R] M'} (hf : IsBaseChange S f) : IsBaseChange S (f.compLeft ι)
参数：ι : Type*；hf : IsBaseChange S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.pi`：pi {ι : Type*} [Finite ι] {M M' : ι -> Type*} [forall i
, AddCommMonoid (M i)] [forall i, AddCommMonoid (M' i)] [forall i, Module R (M i
)] [f…
-/
theorem finitePow (ι : Type*) [Finite ι]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {f : M →ₗ[R] M'} (hf : IsBaseChange S f) :
    IsBaseChange S (f.compLeft ι) :=
  IsBaseChange.pi (f := fun _ ↦ f) (fun _ ↦ hf)

end IsBaseChange

namespace IsLocalizedModule

variable (S : Submonoid R)

attribute [local instance] IsLocalizedModule.isScalarTower_module

/-- Localization of modules commutes with binary products. -/
/-
**IsLocalizedModule.prodMap** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalizedModule`。
形式化陈述：prodMap {M N M' N' : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R 
M] [Module R N] [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'
] (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') [IsLocalizedModule S f] [IsLocalizedModule
 S g] : IsLocalizedModule S (f.prodMap g)
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] N'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.isScalarTower_module`：isScalarTower_module (f : M ->ₗ[
R] M') [IsLocalizedModule S f] : letI : Module A M'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `IsBaseChange.prodMap`：prodMap {M N M' N' : Type*} [AddCommMonoid M] [Add
CommMonoid N] [Module R M] [Module R N] [AddCommMonoid M'] [AddCommMonoid N'] [M
odule R M'…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Localization of modules commutes with binary products.
-/
instance prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  let : Module (Localization S) M' := IsLocalizedModule.module S f
  let : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

/-- Localization of modules commutes with finite products. -/
/-
**IsLocalizedModule.pi** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalizedModule`。
形式化陈述：pi {ι : Type*} [Finite ι] {M M' : ι -> Type*} [forall i, AddCommMonoid (M 
i)] [forall i, AddCommMonoid (M' i)] [forall i, Module R (M i)] [forall i, Modul
e R (M' i)] (f : forall i, M i ->ₗ[R] M' i) [forall i, IsLocalizedModule S (f i)
] : IsLocalizedModule S (.pi fun i => f i ∘ₗ .proj i)
参数：M i；M' i；M i；M' i；f : forall i, M i ->ₗ[R] M' i；f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.isScalarTower_module`：isScalarTower_module (f : M ->ₗ[
R] M') [IsLocalizedModule S f] : letI : Module A M'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `IsBaseChange.pi`：pi {ι : Type*} [Finite ι] {M M' : ι -> Type*} [forall i
, AddCommMonoid (M i)] [forall i, AddCommMonoid (M' i)] [forall i, Module R (M i
)] [f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Localization of modules commutes with finite products.
-/
instance pi {ι : Type*} [Finite ι]
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  let (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

end IsLocalizedModule

namespace IsBaseChange

section DirectSum

open TensorProduct LinearMap DirectSum

variable {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    [∀ i, Module S (P i)] [∀ i, IsScalarTower R S (P i)]
    {ε : (i : ι) → N i →ₗ[R] P i}

/-- Base change for direct sums. -/
/-
**IsBaseChange.directSum** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：directSum (ibc : forall i, IsBaseChange S (ε i)) : IsBaseChange S (lmap ε)
参数：ibc : forall i, IsBaseChange S (ε i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TensorProduct.coe_directSumRight`：coe_directSumRight : ⇑(directSumRight 
R S M₁' M₂) = directSumRight R R M₁' M₂
· 使用引理 `TensorProduct.directSumRight_tmul`：directSumRight_tmul (m : M₁') (n : ⨁ 
i, M₂ i) (i : ι₂) : directSumRight R S M₁' M₂ (m otimesₜ[R] n) i = m otimesₜ[R] 
(n i)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Base change for direct sums.
-/
theorem directSum (ibc : ∀ i, IsBaseChange S (ε i)) :
    IsBaseChange S (lmap ε) := by
  classical
  apply of_equiv <| directSumRight R S S N ≪≫ₗ congrLinearEquiv fun i ↦ (ibc i).equiv
  intros; ext
  simp [coe_directSumRight, coe_congrLinearEquiv, equiv_tmul]

variable (ι)
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {ε : M →ₗ[R] M'}

/-- Base change for direct sums of a constant module. -/
/-
**IsBaseChange.directSumPow** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：directSumPow (ibc : IsBaseChange S ε) : IsBaseChange S (lmap fun _ : ι => 
ε)
参数：ibc : IsBaseChange S ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.directSum`：directSum (ibc : forall i, IsBaseChange S (ε i))
 : IsBaseChange S (lmap ε)

--- 原说明 ---
Base change for direct sums of a constant module.
-/
theorem directSumPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (lmap fun _ : ι ↦ ε) :=
  directSum (fun _ : ι ↦ ibc)
/-
**IsBaseChange.finsuppPow** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：finsuppPow (ibc : IsBaseChange S ε) : IsBaseChange S (Finsupp.mapRange.lin
earMap (α
参数：ibc : IsBaseChange S ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `IsBaseChange.directSum`：directSum (ibc : forall i, IsBaseChange S (ε i))
 : IsBaseChange S (lmap ε)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lmap_finsuppLEquivDirectSum_eq`：lmap_finsuppLEquivDirectSum_eq {N : Type
*} [AddCommMonoid N] [Module R N] (ε : M ->ₗ[R] N) (m : ι ->₀ M) : (lmap fun _ =
> ε) ((finsuppLEquiv…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `finsuppLEquivDirectSum_apply`：finsuppLEquivDirectSum_apply (m : ι ->₀ M)
 (i : ι) : finsuppLEquivDirectSum R M ι m i = m i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (Finsupp.mapRange.linearMap (α := ι) ε) := by
  classical
  apply of_equiv <|
    LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
      (directSum (fun _ ↦ ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
  intro x
  rw [LinearEquiv.trans_apply, Finsupp.mapRange.linearMap_apply,
    LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, lmap_finsuppLEquivDirectSum_eq]

end DirectSum

end IsBaseChange

