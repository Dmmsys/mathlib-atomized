/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Topological torsors of groups

This file defines topological torsors of additive and multiplicative groups, that is, torsors where
`+ᵥ` and `-ᵥ` resp. `•` and `/ₛ` are continuous.
-/

@[expose] public section

open Topology

section Torsor

/-- A topological torsor over a topological additive group is a torsor where `+ᵥ` and `-ᵥ` are
continuous. -/
/-
**IsTopologicalAddTorsor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{V : Type u_1} →   [inst : AddGroup V] → [TopologicalSpace V] → (P : Type 
u_2) → [AddTorsor V P] → [TopologicalSpace P] → Prop
参数：P : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological torsor over a topological additive group is a torsor where `+ᵥ` an
d `-ᵥ` are
continuous.
-/
class IsTopologicalAddTorsor {V : Type*} [AddGroup V] [TopologicalSpace V]
    (P : Type*) [AddTorsor V P] [TopologicalSpace P] extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

/-- A topological torsor over a topological group is a torsor where `•` and `/ₛ` are continuous. -/
@[to_additive]
/-
**IsTopologicalTorsor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{V : Type u_1} → [inst : Group V] → [TopologicalSpace V] → (P : Type u_2) 
→ [Torsor V P] → [TopologicalSpace P] → Prop
参数：P : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological torsor over a topological group is a torsor where `•` and `/ₛ` are
 continuous.
-/
class IsTopologicalTorsor {V : Type*} [Group V] [TopologicalSpace V]
    (P : Type*) [Torsor V P] [TopologicalSpace P] extends ContinuousSMul V P where
  continuous_sdiv : Continuous (fun x : P × P => x.1 /ₛ x.2)

variable {V P α : Type*} [Group V] [TopologicalSpace V] [Torsor V P] [TopologicalSpace P]

export IsTopologicalAddTorsor (continuous_vsub)

export IsTopologicalTorsor (continuous_sdiv)

attribute [fun_prop] continuous_vsub continuous_sdiv

variable [IsTopologicalTorsor P]

@[to_additive]
/-
**Filter.Tendsto.sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.sdiv {l : Filter α} {f g : α -> P} {x y : P} (hf : Tendsto 
f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f /ₛ g) l (𝓝 (x /ₛ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `IsTopologicalTorsor.continuous_sdiv`：∀ {V : Type u_1} {inst : Group V} {
inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : To
pologicalSpace P} [self :…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.sdiv {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f /ₛ g) l (𝓝 (x /ₛ y)) :=
  (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[to_additive (attr := fun_prop)]
/-
**Continuous.sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sdiv {f g : α -> P} (hf : Continuous f) (hg : Continuous g) : C
ontinuous (fun x => f x /ₛ g x)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `IsTopologicalTorsor.continuous_sdiv`：∀ {V : Type u_1} {inst : Group V} {
inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : To
pologicalSpace P} [self :…
-/
theorem Continuous.sdiv {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x /ₛ g x) :=
  continuous_sdiv.comp₂ hf hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.sdiv {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ f x /ₛ g x) x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.sdiv {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x /ₛ g x) s x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
/-
**ContinuousOn.sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.sdiv {f g : α -> P} {s : Set α} (hf : ContinuousOn f s) (hg :
 ContinuousOn g s) : ContinuousOn (fun x => f x /ₛ g x) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.sdiv`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} 
[inst : Group V] [inst_1 : TopologicalSpace V] [inst_2 : Torsor V P]   [inst_3 :
 TopologicalS…
-/
theorem ContinuousOn.sdiv {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x /ₛ g x) s := fun x hx ↦
  (hf x hx).sdiv (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
@[to_additive /-- The underlying group of a topological additive torsor is a topological additive
group. This is not an instance, as `P` cannot be inferred. -/]
/-
**IsTopologicalTorsor.to_isTopologicalGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalTorsor.to_isTopologicalGroup : IsTopologicalGroup V where con
tinuous_mul
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
· 使用定理 `Continuous.sdiv`：Continuous.sdiv {f g : α -> P} (hf : Continuous f) (hg 
: Continuous g) : Continuous (fun x => f x /ₛ g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem IsTopologicalTorsor.to_isTopologicalGroup : IsTopologicalGroup V where
  continuous_mul := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

/-- The map `v ↦ v • p` as a homeomorphism between `V` and `P`. -/
@[to_additive (attr := simps!) /-- The map `v ↦ v +ᵥ p` as a homeomorphism between `V` and `P`. -/]
/-
**Homeomorph.smulConst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.smulConst (p : P) : V ≃ₜ P where __
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `v ↦ v • p` as a homeomorphism between `V` and `P`.
-/
def Homeomorph.smulConst (p : P) : V ≃ₜ P where
  __ := Equiv.smulConst p

/-- The map `p' ↦ p /ₛ p'` as a homeomorphism: `Equiv.constSDiv` as a homeomorphism -/
@[to_additive (attr := simps!)
/-- The map `p' ↦ p -ᵥ p'` as a homeomorphism: `Equiv.constVSub` as a homeomorphism -/]
/-
**Homeomorph.constSDiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.constSDiv (p : P) : P ≃ₜ V where toEquiv
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Homeomorph.constSDiv (p : P) : P ≃ₜ V where
  toEquiv := Equiv.constSDiv p
  continuous_invFun := by
    have := IsTopologicalTorsor.to_isTopologicalGroup V P
    fun_prop

/-- `Equiv.pointReflection` as a homeomorphism -/
/-
**Homeomorph.pointReflection** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V]
 [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) : P ≃ₜ 
P
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.pointReflection` as a homeomorphism
-/
def Homeomorph.pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
    [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) : P ≃ₜ P :=
  (Homeomorph.constVSub p).trans (Homeomorph.vaddConst p)

@[simp]
/-
**Homeomorph.coe_pointReflection** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_pointReflection {V P : Type*} [AddGroup V] [TopologicalSpac
e V] [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) : (
Homeomorph.pointReflection p : P -> P) = Equiv.pointReflection p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Homeomorph.coe_pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
    [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) :
    (Homeomorph.pointReflection p : P → P) = Equiv.pointReflection p := rfl

end Torsor

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalTorsor G where
  continuous_sdiv := by simp only [sdiv_eq_div]; fun_prop

end Group

section Prod

variable
  {V W P Q : Type*}
  [CommGroup V] [TopologicalSpace V]
  [Torsor V P] [TopologicalSpace P] [IsTopologicalTorsor P]
  [CommGroup W] [TopologicalSpace W]
  [Torsor W Q] [TopologicalSpace Q] [IsTopologicalTorsor Q]

@[to_additive instIsTopologicalAddTorsorProd]
/-
**instIsTopologicalTorsorProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsTopologicalTorsorProd : IsTopologicalTorsor (P × Q) where continuous
_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.sdiv`：Continuous.sdiv {f g : α -> P} (hf : Continuous f) (hg 
: Continuous g) : Continuous (fun x => f x /ₛ g x)
-/
instance instIsTopologicalTorsorProd : IsTopologicalTorsor (P × Q) where
  continuous_smul := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι → Type*}
  [∀ i, CommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, Torsor (V i) (P i)] [∀ i, TopologicalSpace (P i)] [∀ i, IsTopologicalTorsor (P i)]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalTorsor ((i : ι) → P i) where
  continuous_smul := continuous_pi <| by simp only [Pi.smul_apply']; fun_prop
  continuous_sdiv := continuous_pi <| by simp only [Pi.sdiv_apply]; fun_prop

end Pi

