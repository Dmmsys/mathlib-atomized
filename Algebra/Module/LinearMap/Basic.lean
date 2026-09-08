/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Further results on (semi)linear maps
-/

@[expose] public section


assert_not_exists Submonoid Finset TrivialStar

open Function

universe u u' v w x y z

variable {R R' S M M' : Type*}

namespace LinearMap

section toFunAsLinearMap

variable {R M N A : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N] [SMulCommClass R A N]

variable (R M N A) in
/-- `A`-linearly coerce an `R`-linear map from `M` to `N` to a function, when `N` has
commuting `R`-module and `A`-module structures. -/
/-
**LinearMap.ltoFun** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ltoFun : (M ->ₗ[R] N) ->ₗ[A] (M -> N) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A`-linearly coerce an `R`-linear map from `M` to `N` to a function, when `N` ha
s
commuting `R`-module and `A`-module structures.
-/
def ltoFun : (M →ₗ[R] N) →ₗ[A] (M → N) where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**LinearMap.ltoFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_6} {M : Type u_7} {N : Type u_8} {A : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring A]   [inst_2 : AddCommMonoid M] [inst_3 : _root_.Modu
le R M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R N]   [inst_6 : _roo
t_.Module A N] [inst_7 : SMulCommClass R A N] {f : M →ₗ[R] N}, (LinearMap.ltoFun
 R M N A) f = ⇑f
参数：LinearMap.ltoFun R M N A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ltoFun_apply {f : M →ₗ[R] N} : ltoFun R M N A f = f := rfl

end toFunAsLinearMap

section SMul

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R →+* R'}

variable {S' T' : Type*}
variable [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M]
variable [Monoid T'] [DistribMulAction T' M] [SMulCommClass R T' M]

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  smul a f :=
    { toFun := a • (f : M → M')
      map_add' := fun x y ↦ by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }
/-
**LinearMap._root_.DomMulAct.smul_linearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DomMulAct.smul_linearMap_apply (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (a • f) x = f (DomMulAct.mk.symm a • x) :=
  rfl

@[simp]
/-
**LinearMap._root_.DomMulAct.mk_smul_linearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DomMulAct.mk_smul_linearMap_apply (a : S') (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (DomMulAct.mk a • f) x = f (a • x) :=
  rfl
/-
**LinearMap._root_.DomMulAct.coe_smul_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DomMulAct.coe_smul_linearMap (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M') :
    (a • f : M →ₛₗ[σ₁₂] M') = a • (f : M → M') :=
  rfl
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') :=
  ⟨fun s t f ↦ ext fun m ↦ by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

end SMul


section Actions

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R →+* R'}

section SMul

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  one_smul _ := ext fun _ ↦ congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ ↦ congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ ↦ rfl
  smul_zero _ := ext fun _ ↦ rfl

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M'] [SMulCommClass R' S M']

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M') :=
  coe_injective.moduleIsTorsionFree _ coe_smul

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by
    simp [DomMulAct.smul_linearMap_apply, DomMulAct.mk, MulOpposite.opEquiv]

end Module

end Actions

section mulLeftRight
variable {R A : Type*} [Semiring R]

section nonUnitalSemiring
variable (R A) [NonUnitalSemiring A] [Module R A]

@[simp]
/-
**LinearMap.mulLeft_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeft_mul [SMulCommClass R A A] (a b : A) : mulLeft R (a * b) = (mulLeft
 R a).comp (mulLeft R b)
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]
/-
**LinearMap.mulRight_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulRight_mul [IsScalarTower R A A] (a b : A) : mulRight R (a * b) = (mulRi
ght R b).comp (mulRight R a)
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

end nonUnitalSemiring

section nonAssocSemiring
variable [NonAssocSemiring A] [Module R A]

/-
**LinearMap.mulLeft_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_6} {A : Type u_7} [inst : Semiring R] [inst_1 : NonAssocSemi
ring A] [inst_2 : _root_.Module R A]   [inst_3 : SMulCommClass R A A] {a b : A},
 LinearMap.mulLeft R a = LinearMap.mulLeft R b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
@[simp] lemma mulLeft_inj [SMulCommClass R A A] {a b : A} :
    mulLeft R a = mulLeft R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩
/-
**LinearMap.mulRight_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_6} {A : Type u_7} [inst : Semiring R] [inst_1 : NonAssocSemi
ring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] {a b : A},
 LinearMap.mulRight R a = LinearMap.mulRight R b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
@[simp] lemma mulRight_inj [IsScalarTower R A A] {a b : A} :
    mulRight R a = mulRight R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

section
variable (R A)

@[simp]
/-
**LinearMap.mulLeft_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeft_one [SMulCommClass R A A] : mulLeft R (1 : A) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulLeft_one [SMulCommClass R A A] : mulLeft R (1 : A) = LinearMap.id := ext one_mul

@[simp]
/-
**LinearMap.mulLeft_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeft_eq_zero_iff [SMulCommClass R A A] (a : A) : mulLeft R a = 0 ↔ a = 
0
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mulLeft_inj`：∀ {R : Type u_6} {A : Type u_7} [inst : Semiring 
R] [inst_1 : NonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : SMulCo
mmClass R A…
· 使用定理 `LinearMap.mulLeft_zero_eq_zero`：mulLeft_zero_eq_zero : mulLeft R (0 : A)
 = 0
-/
theorem mulLeft_eq_zero_iff [SMulCommClass R A A] (a : A) : mulLeft R a = 0 ↔ a = 0 :=
  mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]
/-
**LinearMap.mulRight_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulRight_one [IsScalarTower R A A] : mulRight R (1 : A) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mulRight_one [IsScalarTower R A A] : mulRight R (1 : A) = LinearMap.id :=
  ext mul_one

@[simp]
/-
**LinearMap.mulRight_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulRight_eq_zero_iff [IsScalarTower R A A] (a : A) : mulRight R a = 0 ↔ a 
= 0
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mulRight_inj`：∀ {R : Type u_6} {A : Type u_7} [inst : Semiring
 R] [inst_1 : NonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsSca
larTower R A…
· 使用定理 `LinearMap.mulRight_zero_eq_zero`：mulRight_zero_eq_zero : mulRight R (0 :
 A) = 0
-/
theorem mulRight_eq_zero_iff [IsScalarTower R A A] (a : A) : mulRight R a = 0 ↔ a = 0 :=
  mulRight_zero_eq_zero R A ▸ mulRight_inj

end
end nonAssocSemiring
end mulLeftRight

end LinearMap

namespace Sum

variable {ι κ R : Type*} [Semiring R]

/-- The map `Sum.elim` specialised with zero in the first argument, as a linear map. -/
/-
**Sum.elimZeroLeft** 是 Mathlib 中的一个定义，位于命名空间 `Sum`。
形式化陈述：{ι : Type u_6} → {κ : Type u_7} → {R : Type u_8} → [inst : Semiring R] → (
ι → R) →ₗ[R] κ ⊕ ι → R
参数：ι → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Sum.elim` specialised with zero in the first argument, as a linear map.
-/
@[simps] def elimZeroLeft : (ι → R) →ₗ[R] (κ ⊕ ι → R) where
  toFun := Sum.elim 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

/-- The map `Sum.elim` specialised with zero in the second argument, as a linear map. -/
/-
**Sum.elimZeroRight** 是 Mathlib 中的一个定义，位于命名空间 `Sum`。
形式化陈述：{ι : Type u_6} → {κ : Type u_7} → {R : Type u_8} → [inst : Semiring R] → (
ι → R) →ₗ[R] ι ⊕ κ → R
参数：ι → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Sum.elim` specialised with zero in the second argument, as a linear map
.
-/
@[simps] def elimZeroRight : (ι → R) →ₗ[R] (ι ⊕ κ → R) where
  toFun := fun f ↦ Sum.elim f 0
  map_add' f g := by ext (i | i) <;> simp
  map_smul' t f := by ext (i | i) <;> simp

end Sum

