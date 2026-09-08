/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod

/-!
# Further results on (semi)linear equivalences.
-/

@[expose] public section

open Function

variable {R : Type*} {R₂ : Type*}
variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

section AddCommMonoid

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

section RestrictScalars

variable (R)
variable [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `LinearMap.restrictScalars`. -/
@[simps!, simps toLinearMap]
/-
**LinearEquiv.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ where toLinearMap
参数：f : M ≃ₗ[S] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule 
structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), th
en any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `LinearMap.restrictScalars`.
-/
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ where
  toLinearMap := f.toLinearMap.restrictScalars R
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
/-
**LinearEquiv.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (M ≃ₗ[
S] M₂) -> M ≃ₗ[R] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `LinearEquiv.congr_fun`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearEquiv.congr_fun h :)

@[simp]
/-
**LinearEquiv.restrictScalars_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：restrictScalars_inj (f g : M ≃ₗ[S] M₂) : f.restrictScalars R = g.restrictS
calars R ↔ f = g
参数：f g : M ≃ₗ[S] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.restrictScalars_injective`：restrictScalars_injective : Funct
ion.Injective (restrictScalars R : (M ≃ₗ[S] M₂) -> M ≃ₗ[R] M₂)
-/
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

end RestrictScalars

/-
**LinearEquiv._root_.Module.End.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.End.isUnit_iff [Module R M] (f : Module.End R M) :
    IsUnit f ↔ Function.Bijective f :=
  ⟨fun h ↦
    Function.bijective_iff_has_inverse.mpr <|
      ⟨h.unit.inv,
        ⟨Module.End.isUnit_inv_apply_apply_of_isUnit h,
        Module.End.isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H ↦
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, LinearMap.ext e.left_inv⟩, rfl⟩⟩

section Automorphisms

variable [Module R M]

/-
**LinearEquiv.automorphismGroup** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：automorphismGroup : Group (M ≃ₗ[R] M) where mul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance automorphismGroup : Group (M ≃ₗ[R] M) where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  mul_one _ := ext fun _ ↦ rfl
  one_mul _ := ext fun _ ↦ rfl
  inv_mul_cancel f := ext <| f.left_inv
/-
**LinearEquiv.one_eq_refl** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M := rfl
/-
**LinearEquiv.mul_eq_trans** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：mul_eq_trans (f g : M ≃ₗ[R] M) : f * g = g.trans f
参数：f g : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_eq_trans (f g : M ≃ₗ[R] M) : f * g = g.trans f := rfl

@[simp]
/-
**LinearEquiv.coe_one** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_one : ↑(1 : M ≃ₗ[R] M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_one : ↑(1 : M ≃ₗ[R] M) = id := rfl
/-
**LinearEquiv.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : M ≃ₗ[R] M), ⇑f⁻¹ = ⇑f.symm
参数：f : M ≃ₗ[R] M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inv (f : M ≃ₗ[R] M) : ⇑f⁻¹ = ⇑f.symm := rfl

@[simp]
/-
**LinearEquiv.coe_toLinearMap_one** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toLinearMap_one : (↑(1 : M ≃ₗ[R] M) : M ->ₗ[R] M) = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLinearMap_one : (↑(1 : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id := rfl

@[simp]
/-
**LinearEquiv.coe_toLinearMap_mul** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toLinearMap_mul {e₁ e₂ : M ≃ₗ[R] M} : (↑(e₁ * e₂) : M ->ₗ[R] M) = (e₁ 
: M ->ₗ[R] M) * (e₂ : M ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLinearMap_mul {e₁ e₂ : M ≃ₗ[R] M} :
    (↑(e₁ * e₂) : M →ₗ[R] M) = (e₁ : M →ₗ[R] M) * (e₂ : M →ₗ[R] M) :=
  rfl
/-
**LinearEquiv.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_pow (e : M ≃ₗ[R] M) (n : Nat) : ⇑(e ^ n) = e^[n]
参数：e : M ≃ₗ[R] M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
-/
theorem coe_pow (e : M ≃ₗ[R] M) (n : ℕ) : ⇑(e ^ n) = e^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
/-
**LinearEquiv.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：pow_apply (e : M ≃ₗ[R] M) (n : Nat) (m : M) : (e ^ n) m = e^[n] m
参数：e : M ≃ₗ[R] M；n : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LinearEquiv.coe_pow`：coe_pow (e : M ≃ₗ[R] M) (n : Nat) : ⇑(e ^ n) = e^[n
]
-/
theorem pow_apply (e : M ≃ₗ[R] M) (n : ℕ) (m : M) : (e ^ n) m = e^[n] m := congr_fun (coe_pow e n) m
/-
**LinearEquiv.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f g : M ≃ₗ[R] M) (x : M), (f * g) x = f (g 
x)
参数：f g : M ≃ₗ[R] M；x : M；f * g；g x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mul_apply (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
/-
**LinearEquiv.automorphismGroup.toLinearMapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `
LinearEquiv.automorphismGroup`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : Semiring R] → [inst_1 : Ad
dCommMonoid M] → [inst_2 : _root_.Module R M] → (M ≃ₗ[R] M) →* M →ₗ[R] M
参数：M ≃ₗ[R] M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of 
`M`,
promoted to a monoid hom.
-/
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
/-
**LinearEquiv.applyDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**LinearEquiv.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : M ≃ₗ[R] M) (a : M), f • a = f a
参数：f : M ≃ₗ[R] M；a : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl

/-- `LinearEquiv.applyDistribMulAction` is faithful. -/
/-
**LinearEquiv.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'

--- 原说明 ---
`LinearEquiv.applyDistribMulAction` is faithful.
-/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨LinearEquiv.ext⟩
/-
**LinearEquiv.apply_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] : SMulComm
Class S (M ≃ₗ[R] M) M where smul_comm r e m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass S (M ≃ₗ[R] M) M where
  smul_comm r e m := (e.map_smul_of_tower r m).symm
/-
**LinearEquiv.apply_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] : SMulCom
mClass (M ≃ₗ[R] M) S M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass (M ≃ₗ[R] M) S M :=
  SMulCommClass.symm _ _ _

end Automorphisms

section OfSubsingleton

variable (M M₂)
variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
/-
**LinearEquiv.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubsingleton : M ≃ₗ[R] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two modules that are subsingletons are isomorphic.
-/
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M →ₗ[R] M₂) with
    toFun := fun _ ↦ 0
    invFun := fun _ ↦ 0
    left_inv := fun _ ↦ Subsingleton.elim _ _
    right_inv := fun _ ↦ Subsingleton.elim _ _ }

@[simp]
/-
**LinearEquiv.ofSubsingleton_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubsingleton_self : ofSubsingleton M M = refl R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.ofSubsingleton_apply`：∀ {R : Type u_1} (M : Type u_5) (M₂ : 
Type u_7) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id M₂] [inst_3 : _root…
-/
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by
  ext
  simp [eq_iff_true_of_subsingleton]

end OfSubsingleton

end LinearEquiv

namespace Module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
/-
**Module.compHom.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.compHom`。
形式化陈述：{R : Type u_9} → {S : Type u_10} → [inst : Semiring R] → [inst_1 : Semirin
g S] → (g : R ≃+* S) → R ≃ₗ[R] S
参数：g : R ≃+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g : R ≃+* S` is `R`-linear when the module structure on `S` is `Module.compHom 
S g` .
-/
def compHom.toLinearEquiv {R S : Type*} [Semiring R] [Semiring S] (g : R ≃+* S) :
    haveI := compHom S (↑g : R →+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R →+* S)
  { g with
    toFun := (g : R → S)
    invFun := (g.symm : S → R)
    map_smul' := g.map_mul }

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`. -/
@[simps!]
/-
**DistribMulAction.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DistribMulAction`。
形式化陈述：toLinearEquiv (s : S) : M ≃ₗ[R] M
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`.
-/
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, DistribSMul.toLinearMap R M s with }

/-- Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`. -/
@[simps]
/-
**DistribMulAction.toModuleAut** 是 Mathlib 中的一个定义，位于命名空间 `DistribMulAction`。
形式化陈述：toModuleAut : S ->* M ≃ₗ[R] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`.
-/
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' _ _ := LinearEquiv.ext <| mul_smul _ _

end DistribMulAction

/-
**LinearEquiv.smul_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.smul_refl [Semiring R] [Semiring S] [AddCommMonoid M] [Module 
R M] [Module S M] [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M] (α : Sˣ
) : letI
参数：α : Sˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.smul_refl [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M] (α : Sˣ) :
    letI := SMulCommClass.symm R Sˣ M
    α • refl R M = DistribMulAction.toLinearEquiv R M α := rfl

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂]
variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
/-
**AddEquiv.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：toLinearEquiv (h : forall (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂
参数：h : forall (c : R) (x), e (c • x) = c • e x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive equivalence whose underlying function preserves `smul` is a linear e
quivalence.
-/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }

@[simp]
/-
**AddEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_toLinearEquiv (h : forall (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLi
nearEquiv h) = e
参数：h : forall (c : R) (x), e (c • x) = c • e x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl

@[simp]
/-
**AddEquiv.coe_toLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_toLinearEquiv_symm (h : forall (c : R) (x), e (c • x) = c • e x) : ⇑(e
.toLinearEquiv h).symm = e.symm
参数：h : forall (c : R) (x), e (c • x) = c • e x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
/-
**AddEquiv.toNatLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：toNatLinearEquiv : M ≃ₗ[Nat] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive equivalence between commutative additive monoids is a linear equival
ence between
ℕ-modules
-/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a ↦ by rw [map_nsmul]

@[simp]
/-
**AddEquiv.coe_toNatLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl

@[simp]
/-
**AddEquiv.coe_symm_toNatLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_symm_toNatLinearEquiv : ⇑e.toNatLinearEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toNatLinearEquiv : ⇑e.toNatLinearEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**AddEquiv.toNatLinearEquiv_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e :=
  rfl

@[simp]
/-
**AddEquiv._root_.LinearEquiv.toAddEquiv_toNatLinearEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `AddEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e :=
  DFunLike.coe_injective rfl

@[simp]
/-
**AddEquiv.toNatLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toNatLinearEquiv_symm : e.symm.toNatLinearEquiv = e.toNatLinearEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNatLinearEquiv_symm : e.symm.toNatLinearEquiv = e.toNatLinearEquiv.symm :=
  rfl

@[simp]
/-
**AddEquiv.toNatLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.r
efl Nat M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl

@[simp]
/-
**AddEquiv.toNatLinearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) : (e.trans e₂).toNatLinearEquiv = e
.toNatLinearEquiv.trans e₂.toNatLinearEquiv
参数：e₂ : M₂ ≃+ M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toNatLinearEquiv = e.toNatLinearEquiv.trans e₂.toNatLinearEquiv :=
  rfl

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
-- See note [implicit instance arguments]
variable {modM : Module ℤ M} {modM₂ : Module ℤ M₂} {modM₃ : Module ℤ M₃} (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
/-
**AddEquiv.toIntLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：toIntLinearEquiv : M ≃ₗ[Int] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules
-/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ := by
  refine e.toLinearEquiv fun c a ↦ ?_
  convert! e.toAddMonoidHom.map_zsmul c a using 1
  · exact congr(e $(int_smul_eq_zsmul ..))
  · exact int_smul_eq_zsmul ..

@[simp]
/-
**AddEquiv.coe_toIntLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_toIntLinearEquiv : ⇑(e.toIntLinearEquiv (modM
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toIntLinearEquiv : ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)) = e := rfl

@[simp]
/-
**AddEquiv.coe_symm_toIntLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：coe_symm_toIntLinearEquiv : ⇑(e.toIntLinearEquiv (modM
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toIntLinearEquiv :
    ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)).symm = e.symm :=
  rfl

@[simp]
/-
**AddEquiv.toIntLinearEquiv_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e := by
  ext
  rfl

@[simp]
/-
**AddEquiv._root_.LinearEquiv.toAddEquiv_toIntLinearEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `AddEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[ℤ] M₂) :
    AddEquiv.toIntLinearEquiv (e : M ≃+ M₂) = e :=
  DFunLike.coe_injective rfl

@[simp]
/-
**AddEquiv.toIntLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toIntLinearEquiv_symm : e.symm.toIntLinearEquiv (modM
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIntLinearEquiv_symm :
    e.symm.toIntLinearEquiv (modM := modM₂) (modM₂ := modM) = e.toIntLinearEquiv.symm := rfl

@[simp]
/-
**AddEquiv.toIntLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.r
efl Int M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl

@[simp]
/-
**AddEquiv.toIntLinearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) : (e.trans e₂).toIntLinearEquiv (mo
dM
参数：e₂ : M₂ ≃+ M₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toIntLinearEquiv (modM := modM) (modM₂ := modM₃) =
      (e.toIntLinearEquiv (modM₂ := modM₂)).trans e₂.toIntLinearEquiv :=
  rfl

end AddCommGroup

end AddEquiv

namespace LinearMap

/-- Pointwise application of a family of linear forms to a family of vectors -/
/-
**LinearMap.piApply** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：piApply {V : M -> Type*} [CommSemiring R] [forall x, AddCommMonoid (V x)] 
[forall x, Module R (V x)] : (Π x : M, V x ->ₗ[R] R) ->ₗ[R] (Π x : M, V x) ->ₗ[R
] M -> R where toFun e
参数：V x；V x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise application of a family of linear forms to a family of vectors
-/
def piApply {V : M → Type*} [CommSemiring R] [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)] :
    (Π x : M, V x →ₗ[R] R) →ₗ[R] (Π x : M, V x) →ₗ[R] M → R where
  toFun e :=
    { toFun s x := e x (s x)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp]
/-
**LinearMap.piApply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：piApply_apply {V : M -> Type*} [CommSemiring R] [forall x, AddCommMonoid (
V x)] [forall x, Module R (V x)] (e : Π x : M, V x ->ₗ[R] R) (s : Π x : M, V x) 
: piApply e s = fun x => e x (s x)
参数：V x；V x；e : Π x : M, V x ->ₗ[R] R；s : Π x : M, V x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem piApply_apply {V : M → Type*}
    [CommSemiring R] [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)]
    (e : Π x : M, V x →ₗ[R] R) (s : Π x : M, V x) :
    piApply e s = fun x ↦ e x (s x) :=
  rfl

@[simp]
/-
**LinearMap.piApply_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：piApply_apply_apply {V : M -> Type*} [CommSemiring R] [forall x, AddCommMo
noid (V x)] [forall x, Module R (V x)] (e : Π x : M, V x ->ₗ[R] R) (s : Π x : M,
 V x) (x : M) : piApply e s x = e x (s x)
参数：V x；V x；e : Π x : M, V x ->ₗ[R] R；s : Π x : M, V x；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem piApply_apply_apply {V : M → Type*}
    [CommSemiring R] [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)]
    (e : Π x : M, V x →ₗ[R] R) (s : Π x : M, V x) (x : M) :
    piApply e s x = e x (s x) :=
  rfl

variable (R S M)
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This is an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
/-
**LinearMap.ringLmapEquivSelf** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R ->ₗ[R] M) ≃ₗ[S] 
M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable,
 by `R`.

This is an `S`-linear equivalence, under the assumption that `S` acts on `M` com
muting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
def ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with
    toFun := fun f ↦ f 1
    invFun := smulRight (1 : R →ₗ[R] R)
    left_inv := fun f ↦ by
      ext
      simp only [coe_smulRight, Module.End.one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x ↦ by simp }

end LinearMap

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
/-
**addMonoidHomLequivNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoi
d A] [AddCommMonoid B] [Module R B] : (A ->+ B) ≃ₗ[R] A ->ₗ[Nat] B where toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear mo
rphisms `A →ₗ[ℕ] B`.
-/
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
/-
**addMonoidHomLequivInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup
 A] [AddCommGroup B] [Module R B] : (A ->+ B) ≃ₗ[R] A ->ₗ[Int] B where toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear mo
rphisms `A →ₗ[ℤ] B`.
-/
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` and
`ℤ`-module endomorphisms of `A.` -/
/-
**addMonoidEndRingEquivInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(A : Type u_9) → [inst : AddCommGroup A] → AddMonoid.End A ≃+* Module.End 
ℤ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` a
nd
`ℤ`-module endomorphisms of `A.`
-/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ ↦ rfl }

namespace LinearEquiv

section AddCommMonoid

section Subsingleton

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

section Module

variable [Subsingleton M] [Subsingleton M₂]

/-- Between two zero modules, the zero map is an equivalence. -/
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Between two zero modules, the zero map is an equivalence.
-/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M →ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

-- Even though these are implied by `Subsingleton.elim` via the `Unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
@[simp]
/-
**LinearEquiv.zero_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl

@[simp]
/-
**LinearEquiv.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
/-
**LinearEquiv.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

/-- Between two zero modules, the zero map is the only equivalence. -/
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Between two zero modules, the zero map is the only equivalence.
-/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0

end Module

/-
**LinearEquiv.uniqueOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
形式化陈述：uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁
₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance

end Subsingleton

section Uncurry

variable [Semiring R]
variable [AddCommMonoid M] [Module R M]
variable (V V₂ R M)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
/-
**LinearEquiv.curry** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(R : Type u_1) →   (M : Type u_5) →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → (V : Type u_9) → (
V₂ : Type u_10) → (V × V₂ → M) ≃ₗ[R] V → V₂ → M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`.
-/
protected def curry : (V × V₂ → M) ≃ₗ[R] V → V₂ → M :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
/-
**LinearEquiv.coe_curry** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_curry : ⇑(LinearEquiv.curry R M V V₂) = curry
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_curry : ⇑(LinearEquiv.curry R M V V₂) = curry :=
  rfl

@[simp]
/-
**LinearEquiv.coe_curry_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_curry_symm : ⇑(LinearEquiv.curry R M V V₂).symm = uncurry
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_curry_symm : ⇑(LinearEquiv.curry R M V V₂).symm = uncurry :=
  rfl

end Uncurry

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M)


/-- If a linear map has an inverse, it is a linear equivalence. -/
/-
**LinearEquiv.ofLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofLinearMap (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂ wh
ere __
参数：h₁ : f.comp g = .id；h₂ : g.comp f = .id。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a linear map has an inverse, it is a linear equivalence.
-/
def ofLinearMap (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂ where
  __ := f
  invFun := g
  left_inv := LinearMap.ext_iff.1 h₂
  right_inv := LinearMap.ext_iff.1 h₁

@[simp low]
/-
**LinearEquiv.coe_ofLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_ofLinearMap (h₁ h₂) : ⇑(ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f
参数：h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofLinearMap (h₁ h₂) : ⇑(ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[simp low]
/-
**LinearEquiv.symm_ofLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_ofLinearMap (h₁ h₂) : (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = 
(ofLinearMap g f h₂ h₁)
参数：h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_ofLinearMap (h₁ h₂) :
    (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = (ofLinearMap g f h₂ h₁) :=
  rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
@[deprecated ofLinearMap (since := "2026-06-23")]
/-
**LinearEquiv.ofLinear** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofLinear (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂
参数：h₁ : f.comp g = .id；h₂ : g.comp f = .id。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a linear map has an inverse, it is a linear equivalence.
-/
abbrev ofLinear (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂ := ofLinearMap f g h₁ h₂

@[deprecated coe_ofLinearMap (since := "2026-06-23")]
/-
**LinearEquiv.ofLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = 
f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `coe_ofLinearMap`"
  (since := "2026-06-23")]
/-
**LinearEquiv.ofLinear_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofLinear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂
).symm x = g x
参数：x : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) :
    (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `toLinearMap_ofLinearMap`"
  (since := "2026-06-23")]
/-
**LinearEquiv.ofLinear_symm_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofLinear_symm_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).s
ymm = g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinear_symm_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g := rfl

@[simp]
/-
**LinearEquiv.toLinearMap_ofLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_ofLinearMap (h₁ h₂) : (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) 
= f
参数：h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_ofLinearMap (h₁ h₂) : (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[deprecated (since := "2026-08-04")] alias ofLinear_toLinearMap := toLinearMap_ofLinearMap

end

end AddCommMonoid

section Neg

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

/-- `x ↦ -x` as a `LinearEquiv` -/
/-
**LinearEquiv.neg** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：neg : M ≃ₗ[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
`x ↦ -x` as a `LinearEquiv`
-/
def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M →ₗ[R] M) with }

variable {R}

@[simp]
/-
**LinearEquiv.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl
/-
**LinearEquiv.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：neg_apply (x : M) : neg R x = -x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_apply (x : M) : neg R x = -x := by simp

@[simp]
/-
**LinearEquiv.symm_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl

end Neg

section Semiring

open LinearMap

section Semilinear

variable {R₁ R₂ R₁' R₂' : Type*} {M₁ M₂ M₁' M₂' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₁'] [Semiring R₂']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₁'] [AddCommMonoid M₂']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₁' M₁'] [Module R₂' M₂']
variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'}
variable {σ₁₁' : R₁ →+* R₁'} {σ₂₂' : R₂ →+* R₂'}
variable {σ₂₁' : R₂ →+* R₁'} {σ₁₂' : R₁ →+* R₂'}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives an
additive isomorphism between the two function spaces.

See also `LinearEquiv.arrowCongr` for the linear version of this isomorphism. -/
/-
**LinearEquiv.arrowCongrAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R₁ : Type u_9} →   {R₂ : Type u_10} →     {R₁' : Type u_11} →       {R₂' 
: Type u_12} →         {M₁ : Type u_13} →           {M₂ : Type u_14} →          
   {M₁' : Type u_15} →               {M₂' : Type u_16} →                 [inst :
 Semiring R₁] →                   [inst_1 : Semiring R₂] →                     [
inst_2 : Semiring R₁'] →                       [inst_3 : Semiring R₂'] →        
                 [inst_4 : AddCommMonoid M₁] →                           [inst_5
 : AddCommMonoid M₂] →                             [inst_6 : AddCommMonoid M₁'] 
→                               [inst_7 : AddCommMonoid M₂'] →                  
               [inst_8 : _root_.Module R₁ M₁] →                                 
  [inst_9 : _root_.Module R₂ M₂] →                                     [inst_10 
: _root_.Module R₁' M₁'] →                                       [inst_11 : _roo
t_.Module R₂' M₂'] →                                         {σ₁₂ : R₁ →+* R₂} →
                                           {σ₂₁ : R₂ →+* R₁} →                  
                           {σ₁'₂' : R₁' →+* R₂'} →                              
                 {σ₂'₁' : R₂' →+* R₁'} →                                        
         {σ₁₁' : R₁ →+* R₁'} →                                                  
 {σ₂₂' : R₂ →+* R₂'} →                                                     {σ₂₁'
 : R₂ →+* R₁'} →                                                       {σ₁₂' : R
₁ →+* R₂'} →                                                         [inst_12 : 
RingHomInvPair σ₁₂ σ₂₁] →                                                       
    [inst_13 : RingHomInvPair σ₂₁ σ₁₂] →                                        
                     [inst_14 : RingHomInvPair σ₁'₂' σ₂'₁'] →                   
                                            [inst_15 : RingHomInvPair σ₂'₁' σ₁'₂
'] →                                                                 [RingHomCom
pTriple σ₁₁' σ₁'₂' σ₁₂'] →                                                      
             [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂'] →                                
                                     [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] →      
                                                                 [RingHomCompTri
ple σ₁₂ σ₂₁' σ₁₁'] →                                                            
             (M₁ ≃ₛₗ[σ₁₂] M₂) →                                                 
                          (M₁' ≃ₛₗ[σ₁'₂'] M₂') →                                
                                             (M₁ →ₛₗ[σ₁₁'] M₁') ≃+ (M₂ →ₛₗ[σ₂₂']
 M₂')
参数：M₁ ≃ₛₗ[σ₁₂] M₂；M₁' ≃ₛₗ[σ₁'₂'] M₂'；M₁ →ₛₗ[σ₁₁'] M₁'；M₂ →ₛₗ[σ₂₂'] M₂'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isomorphism between the domains and codomains of two spaces of linear m
aps gives an
additive isomorphism between the two function spaces.

See also `LinearEquiv.arrowCongr` for the linear version of this isomorphism.
-/
@[simps] def arrowCongrAddEquiv (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ →ₛₗ[σ₁₁'] M₁') ≃+ (M₂ →ₛₗ[σ₂₂'] M₂') where
  toFun f := (e₂.comp f).comp e₁.symm.toLinearMap
  invFun f := (e₂.symm.comp f).comp e₁.toLinearMap
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]

set_option backward.isDefEq.respectTransparency false in
/-- If `M` and `M₂` are linearly isomorphic then the endomorphism rings of `M` and `M₂`
are isomorphic.

See `LinearEquiv.conj` for the linear version of this isomorphism. -/
/-
**LinearEquiv.conjRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R₁ : Type u_9} →   {R₂ : Type u_10} →     {M₁ : Type u_13} →       {M₂ : 
Type u_14} →         [inst : Semiring R₁] →           [inst_1 : Semiring R₂] →  
           [inst_2 : AddCommMonoid M₁] →               [inst_3 : AddCommMonoid M
₂] →                 [inst_4 : _root_.Module R₁ M₁] →                   [inst_5 
: _root_.Module R₂ M₂] →                     {σ₁₂ : R₁ →+* R₂} →                
       {σ₂₁ : R₂ →+* R₁} →                         [inst_6 : RingHomInvPair σ₁₂ 
σ₂₁] →                           [inst_7 : RingHomInvPair σ₂₁ σ₁₂] → (M₁ ≃ₛₗ[σ₁₂
] M₂) → Module.End R₁ M₁ ≃+* Module.End R₂ M₂
参数：M₁ ≃ₛₗ[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `M₂` are linearly isomorphic then the endomorphism rings of `M` and `
M₂`
are isomorphic.

See `LinearEquiv.conj` for the linear version of this isomorphism.
-/
@[simps!] def conjRingEquiv (e : M₁ ≃ₛₗ[σ₁₂] M₂) : Module.End R₁ M₁ ≃+* Module.End R₂ M₂ where
  __ := arrowCongrAddEquiv e e
  map_mul' _ _ := by ext; simp [arrowCongrAddEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism with respect to an action on the domains. -/
/-
**LinearEquiv.domMulActCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{S : Type u_4} →   {R₁ : Type u_9} →     {R₁' : Type u_11} →       {R₂' : 
Type u_12} →         {M₁ : Type u_13} →           {M₁' : Type u_15} →           
  {M₂' : Type u_16} →               [inst : Semiring R₁] →                 [inst
_1 : Semiring R₁'] →                   [inst_2 : Semiring R₂'] →                
     [inst_3 : AddCommMonoid M₁] →                       [inst_4 : AddCommMonoid
 M₁'] →                         [inst_5 : AddCommMonoid M₂'] →                  
         [inst_6 : _root_.Module R₁ M₁] →                             [inst_7 : 
_root_.Module R₁' M₁'] →                               [inst_8 : _root_.Module R
₂' M₂'] →                                 {σ₁'₂' : R₁' →+* R₂'} →               
                    {σ₂'₁' : R₂' →+* R₁'} →                                     
{σ₁₁' : R₁ →+* R₁'} →                                       {σ₁₂' : R₁ →+* R₂'} 
→                                         [inst_9 : RingHomInvPair σ₁'₂' σ₂'₁'] 
→                                           [inst_10 : RingHomInvPair σ₂'₁' σ₁'₂
'] →                                             [RingHomCompTriple σ₁₁' σ₁'₂' σ
₁₂'] →                                               [inst_12 : Semiring S] →   
                                              [inst_13 : _root_.Module S M₁] →  
                                                 [inst_14 : SMulCommClass R₁ S M
₁] →                                                     [RingHomCompTriple σ₁₂'
 σ₂'₁' σ₁₁'] →                                                       (M₁' ≃ₛₗ[σ₁
'₂'] M₂') →                                                         (M₁ →ₛₗ[σ₁₁'
] M₁') ≃ₗ[Sᵈᵐᵃ] M₁ →ₛₗ[σ₁₂'] M₂'
参数：M₁' ≃ₛₗ[σ₁'₂'] M₂'；M₁ →ₛₗ[σ₁₁'] M₁'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isomorphism between the domains and codomains of two spaces of linear m
aps gives a
linear isomorphism with respect to an action on the domains.
-/
@[simps] def domMulActCongrRight [Semiring S] [Module S M₁]
    [SMulCommClass R₁ S M₁] [RingHomCompTriple σ₁₂' σ₂'₁' σ₁₁']
    (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') : (M₁ →ₛₗ[σ₁₁'] M₁') ≃ₗ[Sᵈᵐᵃ] (M₁ →ₛₗ[σ₁₂'] M₂') where
  __ := arrowCongrAddEquiv (.refl ..) e₂
  map_smul' := DomMulAct.mk.forall_congr_right.mp fun _ _ ↦ by ext; simp

end Semilinear

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
/-
**LinearEquiv.smulOfUnit** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：smulOfUnit (a : Rˣ) : M ≃ₗ[R] M
参数：a : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by a unit `a` of the ring `R` is a linear equivalence.
-/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a

section arrowCongr

-- Difference from above: `R₁` and `R₂` are commutative
/-!
The modules for `arrowCongr` and its lemmas below are related via the semilinearities
```
M₁  ←⎯⎯⎯σ₁₂⎯⎯⎯→ M₂  ←⎯⎯⎯σ₂₃⎯⎯⎯→ M₃
⏐               ⏐               ⏐
σ₁₁'            σ₂₂'            σ₃₃'
↓               ↓               ↓
M₁' ←⎯⎯σ₁'₂'⎯⎯→ M₂' ←⎯⎯σ₂'₃'⎯⎯→ M₃
⏐               ⏐
σ₁'₁''          σ₂'₂''
↓               ↓
M₁''←⎯σ₁''₂''⎯→ M₂''
```
where the horizontal direction corresponds to the `≃ₛₗ`s, and is needed for `arrowCongr_trans`,
while the vertical direction corresponds to the `→ₛₗ`s, and is needed `arrowCongr_comp`.

`Rᵢ` is not necessarily commutative, but `Rᵢ'` and `Rᵢ''` are.
-/
variable {R₁ R₂ R₃ R₁' R₂' R₃' R₁'' R₂'' : Type*} {M₁ M₂ M₃ M₁' M₂' M₃' M₁'' M₂'' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [CommSemiring R₁'] [CommSemiring R₂'] [CommSemiring R₃']
variable [CommSemiring R₁''] [CommSemiring R₂'']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid M₁'] [AddCommMonoid M₂'] [AddCommMonoid M₃']
variable [AddCommMonoid M₁''] [AddCommMonoid M₂'']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₁' M₁'] [Module R₂' M₂'] [Module R₃' M₃']
variable [Module R₁'' M₁''] [Module R₂'' M₂'']
-- horizontal edges and closures
variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}
variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
variable {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁}
variable {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'}
variable {σ₂'₃' : R₂' →+* R₃'} {σ₃'₂' : R₃' →+* R₂'}
variable {σ₁'₃' : R₁' →+* R₃'} {σ₃'₁' : R₃' →+* R₁'}
-- vertical edges and closures
variable {σ₁''₂'' : R₁'' →+* R₂''} {σ₂''₁'' : R₂'' →+* R₁''}
variable {σ₁₁' : R₁ →+* R₁'} {σ₂₂' : R₂ →+* R₂'} {σ₃₃' : R₃ →+* R₃'}
variable {σ₁'₁'' : R₁' →+* R₁''} {σ₂'₂'' : R₂' →+* R₂''}
variable {σ₁₁'' : R₁ →+* R₁''} {σ₂₂'' : R₂ →+* R₂''}
-- diagonals
variable {σ₂₁' : R₂ →+* R₁'} {σ₁₂' : R₁ →+* R₂'}
variable {σ₃₂' : R₃ →+* R₂'} {σ₂₃' : R₂ →+* R₃'}
variable {σ₃₁' : R₃ →+* R₁'} {σ₁₃' : R₁ →+* R₃'}
variable {σ₂'₁'' : R₂' →+* R₁''} {σ₁'₂'' : R₁' →+* R₂''}
variable {σ₂₁'' : R₂ →+* R₁''} {σ₁₂'' : R₁ →+* R₂''}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₂'₃' σ₃'₂'] [RingHomInvPair σ₃'₂' σ₂'₃']
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
variable [RingHomInvPair σ₁'₃' σ₃'₁'] [RingHomInvPair σ₃'₁' σ₁'₃']
variable [RingHomInvPair σ₁''₂'' σ₂''₁''] [RingHomInvPair σ₂''₁'' σ₁''₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₁'' σ₁₁''] [RingHomCompTriple σ₂₂' σ₂'₂'' σ₂₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']
variable [RingHomCompTriple σ₁₁' σ₁'₃' σ₁₃'] [RingHomCompTriple σ₃₁ σ₁₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₁' σ₃₁'] [RingHomCompTriple σ₁₃ σ₃₁' σ₁₁']
variable [RingHomCompTriple σ₂₂' σ₂'₃' σ₂₃'] [RingHomCompTriple σ₃₂ σ₂₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₂' σ₃₂'] [RingHomCompTriple σ₂₃ σ₃₂' σ₂₂']
variable [RingHomCompTriple σ₁₁'' σ₁''₂'' σ₁₂''] [RingHomCompTriple σ₂₁ σ₁₂'' σ₂₂'']
variable [RingHomCompTriple σ₂₂'' σ₂''₁'' σ₂₁''] [RingHomCompTriple σ₁₂ σ₂₁'' σ₁₁'']
variable [RingHomCompTriple σ₁'₁'' σ₁''₂'' σ₁'₂''] [RingHomCompTriple σ₂'₁' σ₁'₂'' σ₂'₂'']
variable [RingHomCompTriple σ₂'₂'' σ₂''₁'' σ₂'₁''] [RingHomCompTriple σ₁'₂' σ₂'₁'' σ₁'₁'']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable [RingHomCompTriple σ₁'₂' σ₂'₃' σ₁'₃'] [RingHomCompTriple σ₃'₂' σ₂'₁' σ₃'₁']

set_option backward.isDefEq.respectTransparency false in
/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces.

See `LinearEquiv.arrowCongrAddEquiv` for the additive version of this isomorphism that works
over a not necessarily commutative semiring. -/
/-
**LinearEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：arrowCongr (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') : (M₁ ->ₛₗ[σ₁₁'
] M₁') ≃ₛₗ[σ₁'₂'] (M₂ ->ₛₗ[σ₂₂'] M₂') where __
参数：e₁ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isomorphism between the domains and codomains of two spaces of linear m
aps gives a
linear isomorphism between the two function spaces.

See `LinearEquiv.arrowCongrAddEquiv` for the additive version of this isomorphis
m that works
over a not necessarily commutative semiring.
-/
def arrowCongr (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ →ₛₗ[σ₁₁'] M₁') ≃ₛₗ[σ₁'₂'] (M₂ →ₛₗ[σ₂₂'] M₂') where
  __ := arrowCongrAddEquiv e₁ e₂
  map_smul' c f := by ext; simp [arrowCongrAddEquiv, map_smulₛₗ]

@[simp]
/-
**LinearEquiv.arrowCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：arrowCongr_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ -
>ₛₗ[σ₁₁'] M₁') (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x))
参数：e₁ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : M₁ ->ₛₗ[σ₁₁'] M₁'；x : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ →ₛₗ[σ₁₁'] M₁')
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/-
**LinearEquiv.arrowCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：arrowCongr_symm_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f :
 M₂ ->ₛₗ[σ₂₂'] M₂') (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x))
参数：e₁ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : M₂ ->ₛₗ[σ₂₂'] M₂'；x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_symm_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₂ →ₛₗ[σ₂₂'] M₂')
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl
/-
**LinearEquiv.arrowCongr_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：arrowCongr_comp (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁''
 ≃ₛₗ[σ₁''₂''] M₂'') (f : M₁ ->ₛₗ[σ₁₁'] M₁') (g : M₁' ->ₛₗ[σ₁'₁''] M₁'') : arrowC
ongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f)
参数：e₁ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂'；e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂''；f : M
₁ ->ₛₗ[σ₁₁'] M₁'；g : M₁' ->ₛₗ[σ₁'₁''] M₁''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrowCongr_comp
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂'')
    (f : M₁ →ₛₗ[σ₁₁'] M₁') (g : M₁' →ₛₗ[σ₁'₁''] M₁'') :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]
/-
**LinearEquiv.arrowCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：arrowCongr_trans (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₁' : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂
 ≃ₛₗ[σ₂₃] M₃) (e₂' : M₂' ≃ₛₗ[σ₂'₃'] M₃') : ((arrowCongr e₁ e₁').trans (arrowCong
r e₂ e₂' : (M₂ ->ₛₗ[σ₂₂'] M₂') ≃ₛₗ[σ₂'₃'] _)) = arrowCongr (e₁.trans e₂) (e₁'.tr
ans e₂')
参数：e₁ : M₁ ≃ₛₗ[σ₁₂] M₂；e₁' : M₁' ≃ₛₗ[σ₁'₂'] M₂'；e₂ : M₂ ≃ₛₗ[σ₂₃] M₃；e₂' : M₂' ≃ₛ
ₗ[σ₂'₃'] M₃'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_trans
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₁' : M₁' ≃ₛₗ[σ₁'₂'] M₂')
    (e₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₂' : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    ((arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂' : (M₂ →ₛₗ[σ₂₂'] M₂') ≃ₛₗ[σ₂'₃'] _)) =
      arrowCongr (e₁.trans e₂) (e₁'.trans e₂') :=
  rfl

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic.

See `LinearEquiv.conjRingEquiv` for the isomorphism between endomorphism rings,
which works over a not necessarily commutative semiring. -/
-- TODO: upgrade to AlgEquiv (but this file currently cannot import AlgEquiv)
/-
**LinearEquiv.conj** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : Module.End R₁' M₁' ≃ₛₗ[σ₁'₂'] Module.End R
₂' M₂'
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : Module.End R₁' M₁' ≃ₛₗ[σ₁'₂'] Module.End R₂' M₂' :=
  arrowCongr e e
/-
**LinearEquiv.conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') : e.conj f = 
((↑e : M₁' ->ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂' ->ₛₗ[σ₂'₁'] M₁')
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : Module.End R₁' M₁'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.conj f = ((↑e : M₁' →ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂' →ₛₗ[σ₂'₁'] M₁') :=
  rfl

-- Note this has lower `simp` priority for performance reasons, so that we rewrite as
-- `e.conj LinearMap.id x => LinearMap.id x` => `x` rather than
-- `e.conj LinearMap.id x => e (LinearMap.id (e.symm x)) => e (e.symm x) => x`.
@[simp 900]
/-
**LinearEquiv.conj_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂
') : e.conj f x = e (f (e.symm x))
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : Module.End R₁' M₁'；x : M₂'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂') :
    e.conj f x = e (f (e.symm x)) :=
  rfl
/-
**LinearEquiv.symm_conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') : e.symm
.conj f = ((↑e.symm : M₂' ->ₛₗ[σ₂'₁'] M₁').comp f).comp (e : M₁' ->ₛₗ[σ₁'₂'] M₂'
)
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : Module.End R₂' M₂'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.symm.conj f = ((↑e.symm : M₂' →ₛₗ[σ₂'₁'] M₁').comp f).comp (e : M₁' →ₛₗ[σ₁'₂'] M₂') :=
  rfl
/-
**LinearEquiv.conj_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_comp (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : Module.End R₁' M₁') : e.conj (g.
comp f) = (e.conj g).comp (e.conj f)
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f g : Module.End R₁' M₁'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.arrowCongr_comp`：arrowCongr_comp (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ :
 M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂'') (f : M₁ ->ₛₗ[σ₁₁'] M₁') (g : 
M₁' ->ₛₗ[σ₁'₁''] …
-/
theorem conj_comp (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : Module.End R₁' M₁') :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g
/-
**LinearEquiv.conj_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_trans (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃') : e₁.conj.t
rans e₂.conj = (e₁.trans e₂).conj
参数：e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂'；e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_trans (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj :=
  rfl
/-
**LinearEquiv.conj_conj_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R₁' : Type u_12} {R₂' : Type u_13} {M₁' : Type u_20} {M₂' : Type u_21} 
[inst : CommSemiring R₁']   [inst_1 : CommSemiring R₂'] [inst_2 : AddCommMonoid 
M₁'] [inst_3 : AddCommMonoid M₂'] [inst_4 : _root_.Module R₁' M₁']   [inst_5 : _
root_.Module R₂' M₂'] {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'} [inst_6 : Ring
HomInvPair σ₁'₂' σ₂'₁']   [inst_7 : RingHomInvPair σ₂'₁' σ₁'₂'] (e : M₁' ≃ₛₗ[σ₁'
₂'] M₂') (f : Module.End R₂' M₂'), e.conj (e.symm.conj f) = f
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : Module.End R₂' M₂'；e.symm.conj f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conj_conj_symm (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.conj (e.symm.conj f) = f := by ext; simp
/-
**LinearEquiv.conj_symm_conj** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R₁' : Type u_12} {R₂' : Type u_13} {M₁' : Type u_20} {M₂' : Type u_21} 
[inst : CommSemiring R₁']   [inst_1 : CommSemiring R₂'] [inst_2 : AddCommMonoid 
M₁'] [inst_3 : AddCommMonoid M₂'] [inst_4 : _root_.Module R₁' M₁']   [inst_5 : _
root_.Module R₂' M₂'] {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'} [inst_6 : Ring
HomInvPair σ₁'₂' σ₂'₁']   [inst_7 : RingHomInvPair σ₂'₁' σ₁'₂'] (e : M₁' ≃ₛₗ[σ₁'
₂'] M₂') (f : Module.End R₁' M₁'), e.symm.conj (e.conj f) = f
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'；f : Module.End R₁' M₁'；e.conj f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conj_symm_conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.symm.conj (e.conj f) = f := by ext; simp

@[simp]
/-
**LinearEquiv.conj_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_id (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : e.conj LinearMap.id = LinearMap.id
参数：e : M₁' ≃ₛₗ[σ₁'₂'] M₂'。
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
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conj_id (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : e.conj LinearMap.id = LinearMap.id := by ext; simp

@[simp]
/-
**LinearEquiv.conj_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：conj_refl (f : Module.End R M) : (refl R M).conj f = f
参数：f : Module.End R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_refl (f : Module.End R M) : (refl R M).conj f = f := rfl

end arrowCongr

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
/-
**LinearEquiv.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：congrRight (f : M₂ ≃ₗ[R] M₃) : (M ->ₗ[R] M₂) ≃ₗ[R] M ->ₗ[R] M₃
参数：f : M₂ ≃ₗ[R] M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from
 `M` into `M₂`
and `M` into `M₃` are linearly isomorphic.
-/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f

variable (M) in
/-- An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-linear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module and an
`S`-module and their actions commute. -/
/-
**LinearEquiv.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(M : Type u_5) →   {M₂ : Type u_7} →     {M₃ : Type u_8} →       [inst : A
ddCommMonoid M] →         [inst_1 : AddCommMonoid M₂] →           [inst_2 : AddC
ommMonoid M₃] →             {R : Type u_9} →               (S : Type u_10) →    
             [inst_3 : Semiring R] →                   [inst_4 : Semiring S] →  
                   [inst_5 : _root_.Module R M₂] →                       [inst_6
 : _root_.Module R M₃] →                         [inst_7 : _root_.Module R M] → 
                          [inst_8 : _root_.Module S M] →                        
     [inst_9 : SMulCommClass R S M] → (M₂ ≃ₗ[R] M₃) → (M₂ →ₗ[R] M) ≃ₗ[S] M₃ →ₗ[R
] M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-l
inear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module 
and an
`S`-module and their actions commute.
-/
@[simps] def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  __ := e.arrowCongrAddEquiv (.refl ..)
  map_smul' _ _ := rfl

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [Module K M]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
/-
**LinearEquiv.smulOfNeZero** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：smulOfNeZero (a : K) (ha : a != 0) : M ≃ₗ[K] M
参数：a : K；ha : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by a nonzero element `a` of the field `K` is a linear equivalence.
-/
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha

end Field

end LinearEquiv

namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
/-
**Equiv.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M -> M₂)) : M ≃ₗ[R] M₂
参数：e : M ≃ M₂；h : IsLinearMap R (e : M -> M₂)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
An equivalence whose underlying function is linear is a linear equivalence.
-/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }

end Equiv

section FunLeft

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable {m n p : Type*}

namespace LinearMap

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
/-
**LinearMap.funLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：funLeft (f : m -> n) : (n -> M) ->ₗ[R] m -> M where toFun
参数：f : m -> n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)`
-/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**LinearMap.funLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：funLeft_apply (f : m -> n) (g : n -> M) (i : m) : funLeft R M f g i = g (f
 i)
参数：f : m -> n；g : n -> M；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funLeft_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl

@[simp]
/-
**LinearMap.funLeft_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：funLeft_id (g : n -> M) : funLeft R M _root_.id g = g
参数：g : n -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funLeft_id (g : n → M) : funLeft R M _root_.id g = g :=
  rfl
/-
**LinearMap.funLeft_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：funLeft_comp (f₁ : n -> p) (f₂ : m -> n) : funLeft R M (f₁ ∘ f₂) = (funLef
t R M f₂).comp (funLeft R M f₁)
参数：f₁ : n -> p；f₂ : m -> n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl
/-
**LinearMap.funLeft_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：funLeft_surjective_of_injective (f : m -> n) (hf : Injective f) : Surjecti
ve (funLeft R M f)
参数：f : m -> n；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.surjective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β} [Nonempty γ],   Function.Injective f → Function.Sur
jective fun g => g ∘ f
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem funLeft_surjective_of_injective (f : m → n) (hf : Injective f) :
    Surjective (funLeft R M f) :=
  hf.surjective_comp_right
/-
**LinearMap.funLeft_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：funLeft_injective_of_surjective (f : m -> n) (hf : Surjective f) : Injecti
ve (funLeft R M f)
参数：f : m -> n；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
-/
theorem funLeft_injective_of_surjective (f : m → n) (hf : Surjective f) :
    Injective (funLeft R M f) :=
  hf.injective_comp_right

end LinearMap

namespace LinearEquiv

open LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
/-
**LinearEquiv.funCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：funCongrLeft (e : m ≃ n) : (n -> M) ≃ₗ[R] m -> M
参数：e : m ≃ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)`
-/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinearMap (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x ↦
      funext fun i ↦ by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x ↦
      funext fun i ↦ by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])

@[simp]
/-
**LinearEquiv.funCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：funCongrLeft_apply (e : m ≃ n) (x : n -> M) : funCongrLeft R M e x = funLe
ft R M e x
参数：e : m ≃ n；x : n -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl

@[simp]
/-
**LinearEquiv.funCongrLeft_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n 
-> M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n → M) :=
  rfl

@[simp]
/-
**LinearEquiv.funCongrLeft_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) : funCongrLeft R M (Equiv.tran
s e₁ e₂) = LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁)
参数：e₁ : m ≃ n；e₂ : n ≃ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl

@[simp]
/-
**LinearEquiv.funCongrLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R
 M e.symm
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl

end LinearEquiv

end FunLeft

section Pi

namespace LinearEquiv

/-- The product over `S ⊕ T` of a family of modules is isomorphic to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `LinearEquiv`.
-/
@[simps -fullyApplied +simpRhs]
/-
**LinearEquiv.sumPiEquivProdPi** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*) (A : S oplus T -> 
Type*) [forall st, AddCommMonoid (A st)] [forall st, Module R (A st)] : (Π (st :
 S oplus T), A st) ≃ₗ[R] (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
 __
参数：R : Type*；S T : Type*；A : S oplus T -> Type*；A st；A st。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product over `S ⊕ T` of a family of modules is isomorphic to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `LinearEquiv`.
-/
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₗ[R] (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The product `Π t : α, f t` of a family of modules is linearly isomorphic to the module
`f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `LinearEquiv`.
-/
@[simps -fullyApplied]
/-
**LinearEquiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*) 
[forall x, AddCommMonoid (f x)] [forall x, Module R (f x)] : (Π t : α, f t) ≃ₗ[R
] f default where __
参数：R : Type*；f : α -> Type*；f x；f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `Π t : α, f t` of a family of modules is linearly isomorphic to the 
module
`f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `LinearEquiv`.
-/
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] : (Π t : α, f t) ≃ₗ[R] f default where
  __ := Equiv.piUnique _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearEquiv

end Pi

namespace Units
variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

variable (R A) in
/-- Left multiplication by a unit of a semiring as a linear equivalence. -/
/-
**Units.mulLeftLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mulLeftLinearEquiv : Aˣ ->* A ≃ₗ[R] A where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Left multiplication by a unit of a semiring as a linear equivalence.
-/
def mulLeftLinearEquiv : Aˣ →* A ≃ₗ[R] A where
  toFun a :=
    { __ := mulLeft a
      __ := LinearMap.mulLeft R (a : A) }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

variable (R) in
/-
**Units.mulLeftLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ (R : Type u_9) {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : SMulCommClass R A A] (a : Aˣ) (x : A),
 ((Units.mulLeftLinearEquiv R A) a) x = ↑a * x
参数：R : Type u_9；a : Aˣ；x : A；(Units.mulLeftLinearEquiv R A) a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mulLeftLinearEquiv_apply (a : Aˣ) (x : A) :
    a.mulLeftLinearEquiv R A x = a * x := rfl

variable (R) in
/-
**Units.symm_mulLeftLinearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：symm_mulLeftLinearEquiv_apply (a : Aˣ) (x : A) : (a.mulLeftLinearEquiv R A
).symm x = a⁻¹ * x
参数：a : Aˣ；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mulLeftLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulLeftLinearEquiv R A).symm x = a⁻¹ * x := rfl
/-
**Units.symm_mulLeftLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : SMulCommClass R A A] (a : Aˣ), ((Units
.mulLeftLinearEquiv R A) a).symm = (Units.mulLeftLinearEquiv R A) a⁻¹
参数：a : Aˣ；(Units.mulLeftLinearEquiv R A) a；Units.mulLeftLinearEquiv R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_mulLeftLinearEquiv (a : Aˣ) :
    (a.mulLeftLinearEquiv R A).symm = a⁻¹.mulLeftLinearEquiv R A := rfl
/-
**Units.mulLeftLinearEquiv_trans_mulLeftLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `U
nits`。
形式化陈述：mulLeftLinearEquiv_trans_mulLeftLinearEquiv (a b : Aˣ) : (a.mulLeftLinearE
quiv R A).trans (b.mulLeftLinearEquiv R A) = .symm (b * a).mulLeftLinearEquiv R 
A
参数：a b : Aˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma mulLeftLinearEquiv_trans_mulLeftLinearEquiv (a b : Aˣ) :
    (a.mulLeftLinearEquiv R A).trans (b.mulLeftLinearEquiv R A) =
      (b * a).mulLeftLinearEquiv R A := map_mul _ _ _ |>.symm
/-
**Units.mulLeftLinearEquiv_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：mulLeftLinearEquiv_mul_apply (u v : Aˣ) (x : A) : mulLeftLinearEquiv R A (
u * v) x = mulLeftLinearEquiv R A u (mulLeftLinearEquiv R A v x)
参数：u v : Aˣ；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulLeftLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    mulLeftLinearEquiv R A (u * v) x =
      mulLeftLinearEquiv R A u (mulLeftLinearEquiv R A v x) := by simp
/-
**Units.toLinearMap_mulLeftLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : SMulCommClass R A A] (u : Aˣ), ↑((Unit
s.mulLeftLinearEquiv R A) u) = LinearMap.mulLeft R ↑u
参数：u : Aˣ；(Units.mulLeftLinearEquiv R A) u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_mulLeftLinearEquiv (u : Aˣ) :
    (mulLeftLinearEquiv R A u).toLinearMap = LinearMap.mulLeft R (u : A) := rfl
/-
**Units.toEquiv_mulLeftLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : SMulCommClass R A A] (u : Aˣ), ((Units
.mulLeftLinearEquiv R A) u).toEquiv = u.mulLeft
参数：u : Aˣ；(Units.mulLeftLinearEquiv R A) u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toEquiv_mulLeftLinearEquiv (u : Aˣ) :
    (mulLeftLinearEquiv R A u).toEquiv = u.mulLeft := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/-- Right multiplication by a unit of a semiring as a linear equivalence. -/
/-
**Units.mulRightLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mulRightLinearEquiv (a : Aˣ) : A ≃ₗ[R] A where __
参数：a : Aˣ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Right multiplication by a unit of a semiring as a linear equivalence.
-/
def mulRightLinearEquiv (a : Aˣ) : A ≃ₗ[R] A where
  __ := mulRight a
  __ := LinearMap.mulRight R (a : A)

variable (R) in
/-
**Units.mulRightLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ (R : Type u_9) {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (a : Aˣ) (x : A),
 (Units.mulRightLinearEquiv R a) x = x * ↑a
参数：R : Type u_9；a : Aˣ；x : A；Units.mulRightLinearEquiv R a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mulRightLinearEquiv_apply (a : Aˣ) (x : A) :
    a.mulRightLinearEquiv R x = x * a := rfl

variable (R) in
/-
**Units.symm_mulRightLinearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：symm_mulRightLinearEquiv_apply (a : Aˣ) (x : A) : (a.mulRightLinearEquiv R
).symm x = x * a⁻¹
参数：a : Aˣ；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mulRightLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulRightLinearEquiv R).symm x = x * a⁻¹ := rfl
/-
**Units.symm_mulRightLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (a : Aˣ), (Units.
mulRightLinearEquiv R a).symm = Units.mulRightLinearEquiv R a⁻¹
参数：a : Aˣ；Units.mulRightLinearEquiv R a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_mulRightLinearEquiv (a : Aˣ) :
    (a.mulRightLinearEquiv R).symm = a⁻¹.mulRightLinearEquiv R := rfl
/-
**Units.mulRightLinearEquiv_trans_mulRightLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`Units`。
形式化陈述：mulRightLinearEquiv_trans_mulRightLinearEquiv (a b : Aˣ) : (a.mulRightLine
arEquiv R).trans (b.mulRightLinearEquiv R) = (a * b).mulRightLinearEquiv R
参数：a b : Aˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulRightLinearEquiv_trans_mulRightLinearEquiv (a b : Aˣ) :
    (a.mulRightLinearEquiv R).trans (b.mulRightLinearEquiv R) =
      (a * b).mulRightLinearEquiv R := by ext; simp [mul_assoc]
/-
**Units.mulRightLinearEquiv_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：mulRightLinearEquiv_mul_apply (u v : Aˣ) (x : A) : mulRightLinearEquiv R (
u * v) x = mulRightLinearEquiv R v (mulRightLinearEquiv R u x)
参数：u v : Aˣ；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulRightLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    mulRightLinearEquiv R (u * v) x =
      mulRightLinearEquiv R v (mulRightLinearEquiv R u x) := by simp [mul_assoc]
/-
**Units.toLinearMap_mulRightLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (u : Aˣ), ↑(Units
.mulRightLinearEquiv R u) = LinearMap.mulRight R ↑u
参数：u : Aˣ；Units.mulRightLinearEquiv R u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_mulRightLinearEquiv (u : Aˣ) :
    (mulRightLinearEquiv R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl
/-
**Units.toEquiv_mulRightLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_9} {A : Type u_10} [inst : Semiring R] [inst_1 : Semiring A]
 [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (u : Aˣ), (Units.
mulRightLinearEquiv R u).toEquiv = u.mulRight
参数：u : Aˣ；Units.mulRightLinearEquiv R u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toEquiv_mulRightLinearEquiv (u : Aˣ) :
    (mulRightLinearEquiv R u).toEquiv = u.mulRight := rfl

end mulRight
end Units

end AddCommMonoid

