/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Algebra

universe u v
variable {R α β : Type*} [Semiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R : Type*) [Zero R] in
/-- Transfer `NoZeroSMulDivisors` across an `Equiv` -/
/-
**Equiv.noZeroSMulDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (e : α ≃ β) (R : Type u_4) [inst : Zero R]
 [inst_1 : Zero β] [inst_2 : SMul R β]   [NoZeroSMulDivisors R β],   have this :
= e.zero;   have this_1 := Equiv.smul R e;   NoZeroSMulDivisors R α
参数：e : α ≃ β；R : Type u_4。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero`：∀ {R : Type u_4} 
{M : Type u_5} {inst : Zero R} {inst_1 : Zero M} {inst_2 : SMul R M} [self : NoZ
eroSMulDivisors R M]   {c : R} {x : M}, c •…

--- 原说明 ---
Transfer `NoZeroSMulDivisors` across an `Equiv`
-/
protected lemma noZeroSMulDivisors [Zero β] [SMul R β] [NoZeroSMulDivisors R β] :
    let := e.zero
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m ↦ ?_⟩
  simpa [smul_def, zero_def, Equiv.eq_symm_apply] using eq_zero_or_eq_zero_of_smul_eq_zero

variable (R) in
/-- Transfer `Module` across an `Equiv` -/
/-
**Equiv.module** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(R : Type u_1) →   {α : Type u_2} →     {β : Type u_3} →       [inst : Sem
iring R] → (e : α ≃ β) → [inst_1 : AddCommMonoid β] → [_root_.Module R β] → _roo
t_.Module R α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Module` across an `Equiv`
-/
protected abbrev module (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    Module R α :=
  letI := Equiv.addCommMonoid e
  { Equiv.distribMulAction R e with
    zero_smul := by simp [smul_def, zero_smul, zero_def]
    add_smul := by simp [add_def, smul_def, add_smul] }

variable (R) in
/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
/-
**Equiv.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] : letI
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    α ≃ₗ[R] β :=
  letI := Equiv.addCommMonoid e
  letI module := Equiv.module R e
  { Equiv.addEquiv e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mp (eq_symm_apply _) rfl }

@[simp]
/-
**Equiv.linearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：linearEquiv_apply (a : α) [AddCommMonoid β] [Module R β] : e.linearEquiv R
 a = e a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearEquiv_apply (a : α) [AddCommMonoid β] [Module R β] :
    e.linearEquiv R a = e a := rfl

@[simp]
/-
**Equiv.linearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：linearEquiv_symm_apply (b : β) [AddCommMonoid β] [Module R β] : letI
参数：b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearEquiv_symm_apply (b : β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    (e.linearEquiv R).symm b = e.symm b := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Transfer `Module.IsTorsionFree` across an `Equiv` -/
/-
**Equiv.moduleIsTorsionFree** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ (R : Type u_1) {α : Type u_2} {β : Type u_3} [inst : Semiring R] (e : α 
≃ β) [inst_1 : AddCommMonoid β]   [inst_2 : _root_.Module R β] [Module.IsTorsion
Free R β],   let this := e.addCommMonoid;   have this_1 := Equiv.module R e;   M
odule.IsTorsionFree R α
参数：R : Type u_1；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transfer `Module.IsTorsionFree` across an `Equiv`
-/
protected lemma moduleIsTorsionFree (e : α ≃ β) [AddCommMonoid β] [Module R β]
    [Module.IsTorsionFree R β] :
    let := e.addCommMonoid
    let := e.module R
    Module.IsTorsionFree R α := by
  extract_lets; exact (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)

end Equiv

variable (A) [Semiring A] [Module R A] [AddCommMonoid α] [AddCommMonoid β] [Module A β]

/-- Transport a module instance via an isomorphism of the underlying abelian groups.
This has better definitional properties than `Equiv.module` since here
the abelian group structure remains unmodified. -/
/-
**AddEquiv.module** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddEquiv.module (e : α ≃+ β) : Module A α where toSMul
参数：e : α ≃+ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a module instance via an isomorphism of the underlying abelian groups.
This has better definitional properties than `Equiv.module` since here
the abelian group structure remains unmodified.
-/
abbrev AddEquiv.module (e : α ≃+ β) : Module A α where
  toSMul := e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

/-- The module instance from `AddEquiv.module` is compatible with the `R`-module structures,
if the `AddEquiv` is induced by an `R`-module isomorphism. -/
/-
**LinearEquiv.isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β] 
(e : α ≃ₗ[R] β) : letI
参数：e : α ≃ₗ[R] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x

--- 原说明 ---
The module instance from `AddEquiv.module` is compatible with the `R`-module str
uctures,
if the `AddEquiv` is induced by an `R`-module isomorphism.
-/
lemma LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β]
    (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  let := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

/-- When `α` is equipped with the `A`-module structure transferred via `e : α ≃+ β`,
this isomorphism is `A`-linear. -/
@[simps]
/-
**AddEquiv.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.linearEquiv (e : α ≃+ β) : letI
参数：e : α ≃+ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is equipped with the `A`-module structure transferred via `e : α ≃+ β`,
this isomorphism is `A`-linear.
-/
def AddEquiv.linearEquiv (e : α ≃+ β) :
    letI := e.module A
    α ≃ₗ[A] β :=
  letI := e.module A
  { __ := e
    map_smul' _ _ := e.apply_symm_apply _ }
