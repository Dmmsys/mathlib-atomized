/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer topological algebraic structures across `Equiv`s

In this file, we construct a continuous linear equivalence `α ≃L[R] β` from an equivalence `α ≃ β`,
where the continuous `R`-module structure on `α` is the one obtained by transporting an
`R`-module structure on `β` back along `e`.
We also specialize this construction to `Shrink α`.

This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {R α β : Type*}

namespace Equiv

variable (e : α ≃ β)

variable [TopologicalSpace β] [AddCommMonoid β] [Semiring R] [Module R β]

variable (R) in
/-- An equivalence `e : α ≃ β` gives a continuous linear equivalence `α ≃L[R] β`
where the continuous `R`-module structure on `α` is the one obtained by transporting an
`R`-module structure on `β` back along `e`.

This is `e.linearEquiv` as a continuous linear equivalence. -/
/-
**Equiv.continuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：continuousLinearEquiv (e : α ≃ β) : letI
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` gives a continuous linear equivalence `α ≃L[R] β`
where the continuous `R`-module structure on `α` is the one obtained by transpor
ting an
`R`-module structure on `β` back along `e`.

This is `e.linearEquiv` as a continuous linear equivalence.
-/
def continuousLinearEquiv (e : α ≃ β) :
    letI := e.topologicalSpace
    letI := e.addCommMonoid
    letI := e.module R
    α ≃L[R] β :=
  letI := e.topologicalSpace
  letI := e.addCommMonoid
  letI := e.module R
  { toLinearEquiv := e.linearEquiv _
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp +instances only [Equiv.topologicalSpace, toFun_as_coe, ← coinduced_symm]
      exact continuous_coinduced_rng }

@[simp]
/-
**Equiv.toLinearEquiv_continuousLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：toLinearEquiv_continuousLinearEquiv (e : α ≃ β) : letI
参数：e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearEquiv_continuousLinearEquiv (e : α ≃ β) :
    letI := e.topologicalSpace
    letI := e.addCommMonoid
    letI := e.module R
    (e.continuousLinearEquiv R).toLinearEquiv = e.linearEquiv R := rfl

end Equiv

section ContinuousLinearEquiv

variable [Semiring R]

/-- Given a continuous multiplicative equivalence `e : α ≃ₜ* β`, if `β` is a topological group,
then so is `α`. -/
@[to_additive
/-- Given a continuous additive equivalence `e : α ≃ₜ+ β`, if `β` is a topological additive group,
then so is `α`. -/]
/-
**ContinuousMulEquiv.isTopologicalGroup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMulEquiv.isTopologicalGroup [TopologicalSpace β] [Group β] [IsTo
pologicalGroup β] [TopologicalSpace α] [Group α] (e : α ≃ₜ* β) : IsTopologicalGr
oup α where continuous_mul
参数：e : α ≃ₜ* β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
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
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `ContinuousMulEquiv.instMulEquivClass`：∀ {M : Type u_1} {N : Type u_2} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst
_3 : Mul N], MulEquivClass…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃ₜ* N) (x :
 M) : e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
lemma ContinuousMulEquiv.isTopologicalGroup
    [TopologicalSpace β] [Group β] [IsTopologicalGroup β] [TopologicalSpace α] [Group α]
    (e : α ≃ₜ* β) : IsTopologicalGroup α where
  continuous_mul := by
    let f := (fun q ↦ q.1 * q.2 : β × β → β)
    have : Continuous (fun p ↦ e.symm <| f (e p.1, e p.2) : (α × α → α)) := by fun_prop
    exact this.congr <| fun p ↦ by simp [f]
  continuous_inv := by
    have : Continuous (e.symm ∘ (fun q ↦ q⁻¹) ∘ e) := by fun_prop
    exact this.congr (fun p ↦ by simp)

/-- Given a continuous linear equivalence `e : α ≃L[R] β`, if scalar multiplication on `β` is
continuous, then so is it for `α`. -/
/-
**ContinuousLinearEquiv.continuousSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.continuousSMul [TopologicalSpace β] [AddCommGroup β]
 [Module R β] [TopologicalSpace R] [ContinuousSMul R β] [TopologicalSpace α] [Ad
dCommGroup α] [Module R α] (e : α ≃L[R] β) : ContinuousSMul R α where continuous
_smul
参数：e : α ≃L[R] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a continuous linear equivalence `e : α ≃L[R] β`, if scalar multiplication 
on `β` is
continuous, then so is it for `α`.
-/
lemma ContinuousLinearEquiv.continuousSMul
    [TopologicalSpace β] [AddCommGroup β] [Module R β] [TopologicalSpace R] [ContinuousSMul R β]
    [TopologicalSpace α] [AddCommGroup α] [Module R α]
    (e : α ≃L[R] β) :
    ContinuousSMul R α where
  continuous_smul := by
    let f : R × α → α := fun p ↦ e.symm <| p.1 • (e p.2)
    have : Continuous f := by fun_prop
    exact this.congr (fun p ↦ by simp [f])

end ContinuousLinearEquiv

universe v

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves the continuous module structure. -/
@[simps!]
/-
**Shrink.continuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Shrink.continuousLinearEquiv [Small.{v} α] [AddCommMonoid α] [TopologicalS
pace α] [Semiring R] [Module R α] : Shrink.{v} α ≃L[R] α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Shrinking `α` to a smaller universe preserves the continuous module structure.
-/
noncomputable def Shrink.continuousLinearEquiv
    [Small.{v} α] [AddCommMonoid α] [TopologicalSpace α] [Semiring R] [Module R α] :
    Shrink.{v} α ≃L[R] α :=
  (equivShrink α).symm.continuousLinearEquiv R
