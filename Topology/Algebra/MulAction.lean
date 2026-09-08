/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic

/-!
# Continuous monoid action

In this file we define class `ContinuousSMul`. We say `ContinuousSMul M X` if `M` acts on `X` and
the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `ContinuousSMul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `Units.continuousSMul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `Homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `Continuous.smul`
or `Filter.Tendsto.smul` that provide dot-syntax access to `ContinuousSMul`.
-/

public section

open Topology Pointwise

open Filter

/-- Class `ContinuousSMul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
/-
**ContinuousSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (X : Type u_2) → [SMul M X] → [TopologicalSpace M] → [Top
ologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ContinuousSMul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multipli
cative actions,
including (semi)modules and algebras.
-/
class ContinuousSMul (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The scalar multiplication `(•)` is continuous. -/
  continuous_smul : Continuous fun p : M × X => p.1 • p.2

export ContinuousSMul (continuous_smul)

/-- Class `ContinuousVAdd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
/-
**ContinuousVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (X : Type u_2) → [VAdd M X] → [TopologicalSpace M] → [Top
ologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ContinuousVAdd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive
 actions,
including (semi)modules and algebras.
-/
class ContinuousVAdd (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

attribute [continuity, fun_prop] continuous_smul continuous_vadd

section Main

variable {M X Y α : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

/-
**IsScalarTower.continuousSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsScalarTower.continuousSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N
] [SMul M N] [MulAction N α] [SMul M α] [IsScalarTower M N α] [TopologicalSpace 
M] [TopologicalSpace N] [TopologicalSpace α] [ContinuousSMul M N] [ContinuousSMu
l N α] : ContinuousSMul M α
参数：N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma IsScalarTower.continuousSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace α] [ContinuousSMul M N] [ContinuousSMul N α] : ContinuousSMul M α :=
  { continuous_smul := by
      suffices Continuous (fun p : M × α ↦ (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSMul (ULift M) X :=
  ⟨(continuous_smul (M := M)).comp₂ (continuous_uliftDown.comp continuous_fst) continuous_snd⟩

@[to_additive]
/-
**OrderDual.instContinuousSMul_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instContinuousSMul_right : ContinuousSMul M Xᵒᵈ where continuous
_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instContinuousSMul_right : ContinuousSMul M Xᵒᵈ where
  continuous_smul := continuous_smul (M := M) (X := X)

@[to_additive]
/-
**OrderDual.instContinuousSMul_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instContinuousSMul_left : ContinuousSMul Mᵒᵈ X where continuous_
smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instContinuousSMul_left : ContinuousSMul Mᵒᵈ X where
  continuous_smul := continuous_smul (M := M) (X := X)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ContinuousSMul.continuousConstSMul : ContinuousConstSMul M X where
  continuous_const_smul _ := continuous_smul.comp (continuous_const.prodMk continuous_id)

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousSMul.induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousSMul.induced {R : Type*} {α : Type*} {β : Type*} {F : Type*} [Fu
nLike F α β] [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Modu
le R β] [TopologicalSpace R] [LinearMapClass F R α β] [tβ : TopologicalSpace β] 
[ContinuousSMul R β] (f : F) : @ContinuousSMul R α _ _ (tβ.induced f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem ContinuousSMul.induced {R : Type*} {α : Type*} {β : Type*} {F : Type*} [FunLike F α β]
    [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    [TopologicalSpace R] [LinearMapClass F R α β] [tβ : TopologicalSpace β] [ContinuousSMul R β]
    (f : F) : @ContinuousSMul R α _ _ (tβ.induced f) := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul]
  fun_prop

@[to_additive]
/-
**Filter.Tendsto.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : Filter α} {c : M} {a : 
X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Tendsto (fun x => f x • g
 x) l (𝓝 <| c • a)
参数：hf : Tendsto f l (𝓝 c)；hg : Tendsto g l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
/-
**Filter.Tendsto.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.smul_const {f : α -> M} {l : Filter α} {c : M} (hf : Tendst
o f l (𝓝 c)) (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a))
参数：hf : Tendsto f l (𝓝 c)；a : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
    (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWi
thinAt g s b) : ContinuousWithinAt (f • g) s b
参数：hf : ContinuousWithinAt f s b；hg : ContinuousWithinAt g s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
-/
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (f • g) s b :=
  Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) : Contin
uousAt (f • g) b
参数：hf : ContinuousAt f b；hg : ContinuousAt g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
-/
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    ContinuousAt (f • g) b :=
  Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Contin
uousOn (f • g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
-/
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f • g) s := fun x hx => (hf x hx).smul (hg x hx)

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/-
**Continuous.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous (f • 
g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous (f • g) :=
  continuous_smul.comp (hf.prodMk hg)

/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
/-
**ContinuousSMul.op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒ
ᵖ X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
instance ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prodMap continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]
/-
**MulOpposite.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
-/
instance MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <|
      continuous_smul.comp <| continuous_id.prodMap MulOpposite.continuous_unop⟩

@[to_additive]
/-
**Specializes.smul** 是 Mathlib 中的一个定理，位于命名空间 `Specializes`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} [inst : TopologicalSpace M] [inst_1 : Topo
logicalSpace X] [inst_2 : SMul M X]   [ContinuousSMul M X] {a b : M} {x y : X}, 
a ⤳ b → x ⤳ y → (a • x) ⤳ (b • y)
参数：a • x；b • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `Specializes.prod`：Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂
) (hy : y₁ ⤳ y₂) : (x₁, y₁) ⤳ (x₂, y₂)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
protected theorem Specializes.smul {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y) :
    (a • x) ⤳ (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
/-
**Inseparable.smul** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} [inst : TopologicalSpace M] [inst_1 : Topo
logicalSpace X] [inst_2 : SMul M X]   [ContinuousSMul M X] {a b : M} {x y : X}, 
Inseparable a b → Inseparable x y → Inseparable (a • x) (b • y)
参数：a • x；b • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
protected theorem Inseparable.smul {a b : M} {x y : X} (h₁ : Inseparable a b)
    (h₂ : Inseparable x y) : Inseparable (a • x) (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
/-
**IsCompact.smul_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsCompact k) (hu : IsComp
act u) : IsCompact (k • u)
参数：hk : IsCompact k；hu : IsCompact u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_smul_prod`：image_smul_prod : (fun x : α × β => x.fst • x.snd) 
'' s ×ˢ t = s • t
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
lemma IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsCompact k) (hu : IsCompact u) :
    IsCompact (k • u) := by
  rw [← Set.image_smul_prod]
  exact IsCompact.image (hk.prod hu) continuous_smul

@[to_additive]
/-
**smul_set_closure_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_set_closure_subset (K : Set M) (L : Set X) : closure K • closure L su
bseteq closure (K • L)
参数：K : Set M；L : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_subset_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {
s : Set α} {t u : Set β}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
· 使用定理 `map_mem_closure₂`：map_mem_closure₂ {f : X -> Y -> Z} {x : X} {y : Y} {s 
: Set X} {t : Set Y} {u : Set Z} (hf : Continuous (uncurry f)) (hx : x in closur
e s) (…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
-/
lemma smul_set_closure_subset (K : Set M) (L : Set X) :
    closure K • closure L ⊆ closure (K • L) :=
  Set.smul_subset_iff.2 fun _x hx _y hy ↦ map_mem_closure₂ continuous_smul hx hy fun _a ha _b hb ↦
    Set.smul_mem_smul ha hb

/-- Suppose that `N` acts on `X` and `M` continuously acts on `Y`.
Suppose that `g : Y → X` is an action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c • x) = f c • g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `MulActionHom`.
However, this version also works for semilinear maps and `f = Units.val`. -/
@[to_additive
  /-- Suppose that `N` additively acts on `X` and `M` continuously additively acts on `Y`.
Suppose that `g : Y → X` is an additive action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c +ᵥ x) = f c +ᵥ g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `AddActionHom`.
However, this version also works for `f = AddUnits.val`. -/]
/-
**Topology.IsInducing.continuousSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousSMul {N : Type*} [SMul N Y] [TopologicalSpac
e N] {f : N -> M} (hg : IsInducing g) (hf : Continuous f) (hsmul : forall {c x},
 g (c • x) = f c • g x) : ContinuousSMul N Y where continuous_smul
参数：hg : IsInducing g；hf : Continuous f；hsmul : forall {c x}, g (c • x) = f c • g
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
lemma Topology.IsInducing.continuousSMul {N : Type*} [SMul N Y] [TopologicalSpace N] {f : N → M}
    (hg : IsInducing g) (hf : Continuous f) (hsmul : ∀ {c x}, g (c • x) = f c • g x) :
    ContinuousSMul N Y where
  continuous_smul := by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
      using (hf.comp continuous_fst).fun_smul <| hg.continuous.comp continuous_snd

@[to_additive]
/-
**SMulMemClass.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulMemClass.continuousSMul {S : Type*} [SetLike S X] [SMulMemClass S M X]
 (s : S) : ContinuousSMul M s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousSMul`：Topology.IsInducing.continuousSMul {
N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M} (hg : IsInducing g) (hf 
: Continuous f) (hsmul :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
instance SMulMemClass.continuousSMul {S : Type*} [SetLike S X] [SMulMemClass S M X] (s : S) :
    ContinuousSMul M s :=
  IsInducing.subtypeVal.continuousSMul continuous_id rfl

end SMul

section SMulZeroClass

variable [Zero X] [SMulZeroClass M X] [ContinuousSMul M X]

/-
**Filter.Tendsto.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} [inst : TopologicalSpace M]
 [inst_1 : TopologicalSpace X]   [inst_2 : Zero X] [inst_3 : SMulZeroClass M X] 
[ContinuousSMul M X] {f : α → M} {g : α → X} {l : Filter α} {c : M},   Filter.Te
ndsto f l (nhds c) → Filter.Tendsto g l (nhds 0) → Filter.Tendsto (fun x => f x 
• g x) l (nhds 0)
参数：nhds c；nhds 0；fun x => f x • g x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
protected theorem Filter.Tendsto.smul_zero {f : α → M} {g : α → X} {l : Filter α} {c : M}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x • g x) l (𝓝 0) :=
  smul_zero c (A := X) ▸ hf.smul hg

end SMulZeroClass

section SMulWithZero

variable [Zero M] [Zero X] [SMulWithZero M X] [ContinuousSMul M X]

/-
**Filter.Tendsto.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} [inst : TopologicalSpace M]
 [inst_1 : TopologicalSpace X]   [inst_2 : Zero M] [inst_3 : Zero X] [inst_4 : S
MulWithZero M X] [ContinuousSMul M X] {f : α → M} {g : α → X}   {l : Filter α} {
a : X},   Filter.Tendsto f l (nhds 0) → Filter.Tendsto g l (nhds a) → Filter.Ten
dsto (fun x => f x • g x) l (nhds 0)
参数：nhds 0；nhds a；fun x => f x • g x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
protected theorem Filter.Tendsto.zero_smul {f : α → M} {g : α → X} {l : Filter α} {a : X}
    (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x ↦ f x • g x) l (𝓝 0) :=
  zero_smul M a ▸ hf.smul hg
/-
**Filter.Tendsto.zero_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} [inst : TopologicalSpace M]
 [inst_1 : TopologicalSpace X]   [inst_2 : Zero M] [inst_3 : Zero X] [inst_4 : S
MulWithZero M X] [ContinuousSMul M X] {f : α → M} {l : Filter α},   Filter.Tends
to f l (nhds 0) → ∀ (a : X), Filter.Tendsto (fun x => f x • a) l (nhds 0)
参数：nhds 0；a : X；fun x => f x • a；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.zero_smul`：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4}
 [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Zero M] [
inst_3 : Zero …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem Filter.Tendsto.zero_smul_const {f : α → M} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (a : X) :
    Tendsto (fun x ↦ f x • a) l (𝓝 0) :=
  hf.zero_smul tendsto_const_nhds

end SMulWithZero

section Monoid

variable [Monoid M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
/-
**Filter.Tendsto.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} [inst : TopologicalSpace M]
 [inst_1 : TopologicalSpace X]   [inst_2 : Monoid M] [inst_3 : MulAction M X] [C
ontinuousSMul M X] {f : α → M} {g : α → X} {l : Filter α} {a : X},   Filter.Tend
sto f l (nhds 1) → Filter.Tendsto g l (nhds a) → Filter.Tendsto (fun x => f x • 
g x) l (nhds a)
参数：nhds 1；nhds a；fun x => f x • g x；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
protected theorem Filter.Tendsto.one_smul {f : α → M} {g : α → X} {l : Filter α} {a : X}
    (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x ↦ f x • g x) l (𝓝 a) :=
  one_smul M a ▸ hf.smul hg

@[to_additive]
/-
**Filter.Tendsto.one_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} [inst : TopologicalSpace M]
 [inst_1 : TopologicalSpace X]   [inst_2 : Monoid M] [inst_3 : MulAction M X] [C
ontinuousSMul M X] {f : α → M} {l : Filter α},   Filter.Tendsto f l (nhds 1) → ∀
 (a : X), Filter.Tendsto (fun x => f x • a) l (nhds a)
参数：nhds 1；a : X；fun x => f x • a；nhds a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.one_smul`：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Monoid M] 
[inst_3 : Mul…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem Filter.Tendsto.one_smul_const {f : α → M} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (a : X) : Tendsto (fun x ↦ f x • a) l (𝓝 a) :=
  hf.one_smul tendsto_const_nhds

@[to_additive]
/-
**Units.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.continuousSMul : ContinuousSMul Mˣ X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousSMul`：Topology.IsInducing.continuousSMul {
N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M} (hg : IsInducing g) (hf 
: Continuous f) (hsmul :…
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
-/
instance Units.continuousSMul : ContinuousSMul Mˣ X :=
  IsInducing.id.continuousSMul Units.continuous_val rfl

/-- If an action is continuous, then composing this action with a continuous homomorphism gives
again a continuous action. -/
@[to_additive]
/-
**MulAction.continuousSMul_compHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.continuousSMul_compHom {N : Type*} [TopologicalSpace N] [Monoid 
N] {f : N ->* M} (hf : Continuous f) : letI : MulAction N X
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
If an action is continuous, then composing this action with a continuous homomor
phism gives
again a continuous action.
-/
theorem MulAction.continuousSMul_compHom
    {N : Type*} [TopologicalSpace N] [Monoid N] {f : N →* M} (hf : Continuous f) :
    letI : MulAction N X := MulAction.compHom _ f
    ContinuousSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp continuous_fst).smul continuous_snd⟩

@[to_additive]
/-
**Submonoid.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.continuousSMul {S : Submonoid M} : ContinuousSMul S X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousSMul`：Topology.IsInducing.continuousSMul {
N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M} (hg : IsInducing g) (hf 
: Continuous f) (hsmul :…
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
instance Submonoid.continuousSMul {S : Submonoid M} : ContinuousSMul S X :=
  IsInducing.id.continuousSMul continuous_subtype_val rfl

end Monoid

section Group

variable [Group M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
/-
**Subgroup.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.continuousSMul {S : Subgroup M} : ContinuousSMul S X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subgroup.continuousSMul {S : Subgroup M} : ContinuousSMul S X :=
  S.toSubmonoid.continuousSMul

variable (M)

/-- The stabilizer of a continuous group action on a discrete space is an open subgroup. -/
/-
**stabilizer_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOpen (MulAction.stabili
zer M x : Set M)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s

--- 原说明 ---
The stabilizer of a continuous group action on a discrete space is an open subgr
oup.
-/
lemma stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOpen (MulAction.stabilizer M x : Set M) :=
  IsOpen.preimage (f := fun g ↦ g • x) (by fun_prop) (isOpen_discrete {x})

end Group

section IsTopologicalGroup

variable [Group M] [IsTopologicalGroup M] [MulAction M X]

/-- A group action of a topological group on a discrete space is continuous if and only if
each stabilizer is an open subgroup. -/
/-
**continuousSMul_iff_stabilizer_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_iff_stabilizer_isOpen [DiscreteTopology X] : ContinuousSMul
 M X ↔ forall x : X, IsOpen (MulAction.stabilizer M x : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_prod_of_discrete_right`：continuous_prod_of_discrete_right [Di
screteTopology β] {f : α × β -> γ} : Continuous f ↔ forall b, Continuous (f ⟨·, 
b⟩)
· 使用定理 `continuous_discrete_rng`：continuous_discrete_rng {α} [TopologicalSpace α
] [TopologicalSpace β] [DiscreteTopology β] {f : α -> β} : Continuous f ↔ forall
 b : β, IsOpe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_empty_ne`：nonempty_iff_empty_ne : s.Nonempty ↔ ∅ != s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G

--- 原说明 ---
A group action of a topological group on a discrete space is continuous if and o
nly if
each stabilizer is an open subgroup.
-/
theorem continuousSMul_iff_stabilizer_isOpen [DiscreteTopology X] :
    ContinuousSMul M X ↔ ∀ x : X, IsOpen (MulAction.stabilizer M x : Set M) := by
  refine ⟨fun _ _ ↦ stabilizer_isOpen .., fun h ↦ ⟨?_⟩⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  let U := {m' : M | m' • y = x}
  have hU : IsOpen U := by
    by_cases hU' : U ≠ ∅
    · obtain ⟨m, (hm : m • y = x)⟩ := Set.nonempty_iff_empty_ne.mpr hU'.symm
      convert! (h x).preimage (by fun_prop : Continuous fun m' : M ↦ m' * m⁻¹)
      ext; simp [← smul_smul, U, eq_inv_smul_iff.mpr hm]
    simp_all
  simpa using! hU

end IsTopologicalGroup

section GroupWithZero

variable {G₀ X : Type*} [GroupWithZero G₀] [Zero X] [MulActionWithZero G₀ X]
  [TopologicalSpace G₀] [(𝓝[≠] (0 : G₀)).NeBot] [TopologicalSpace X] [ContinuousSMul G₀ X]

/-
**Set.univ_smul_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.univ_smul_nhds_zero {s : Set X} (hs : s in 𝓝 0) : (univ : Set G₀) • s 
= Set.univ
参数：hs : s in 𝓝 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem Set.univ_smul_nhds_zero {s : Set X} (hs : s ∈ 𝓝 0) : (univ : Set G₀) • s = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) :=
    zero_smul G₀ x ▸ tendsto_id.smul tendsto_const_nhds
  rcases Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs)
    with ⟨c, hc₀, hc⟩
  simp only [mem_compl_iff, mem_singleton_iff] at hc₀
  simp only [mem_smul, mem_univ, true_and]
  exact ⟨c⁻¹, c • x, hc, inv_smul_smul₀ hc₀ _⟩

@[simp]
/-
**Filter.top_smul_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.top_smul_nhds_zero : (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.eq_top_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l = ⊤ ↔ ∀ (i : ι), p i → 
s i = Set.univ)
· 使用定理 `Filter.HasBasis.smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] 
{f : Filter α} {g : Filter β} {ιf : Type u_7} {ιg : Type u_8}   {pf : ιf → Prop}
 {sf : ιf …
· 使用引理 `Filter.hasBasis_top`：hasBasis_top : (⊤ : Filter α).HasBasis (fun _ : Uni
t => True) (fun _ => Set.univ)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Set.univ_smul_nhds_zero`：Set.univ_smul_nhds_zero {s : Set X} (hs : s in 
𝓝 0) : (univ : Set G₀) • s = Set.univ
-/
theorem Filter.top_smul_nhds_zero : (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤ := by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact Set.univ_smul_nhds_zero hs

end GroupWithZero

@[to_additive]
/-
**Prod.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.continuousSMul [SMul M X] [SMul M Y] [ContinuousSMul M X] [Continuous
SMul M Y] : ContinuousSMul M (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
instance Prod.continuousSMul [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y] :
    ContinuousSMul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousSMul M (γ i)] : ContinuousSMul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <|
        continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {γ : ι → Type*} [Π i, TopologicalSpace (γ i)]
    {N : ι → Type*} [Π i, TopologicalSpace (N i)] [Π i, SMul (N i) (γ i)]
    [∀ i, ContinuousSMul (N i) (γ i)] : ContinuousSMul (Π i, N i) (Π i, γ i) :=
  ⟨continuous_pi fun i ↦ ((continuous_apply i).comp continuous_id'.fst).smul
    ((continuous_apply i).comp continuous_id'.snd)⟩

end Main

section LatticeOps

variable {ι : Sort*} {M X : Type*} [TopologicalSpace M] [SMul M X]

@[to_additive]
/-
**continuousSMul_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_sInf {ts : Set (TopologicalSpace X)} (h : forall t in ts, @
ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf ts)
参数：TopologicalSpace X；h : forall t in ts, @ContinuousSMul M X _ _ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_singleton`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {a : 
α}, sInf {a} = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sInf_rng`：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : 
Set (TopologicalSpace β)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous
[t₁, t] f
· 使用定理 `continuous_sInf_dom₂`：continuous_sInf_dom₂ {X Y Z} {f : X -> Y -> Z} {ta
s : Set (TopologicalSpace X)} {tbs : Set (TopologicalSpace Y)} {tX : Topological
Space X} {…
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
theorem continuousSMul_sInf {ts : Set (TopologicalSpace X)}
    (h : ∀ t ∈ ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf ts) :=
  let _ := sInf ts
  { continuous_smul := by
      -- Porting note: needs `( :)`
      rw [← (sInf_singleton (a := ‹TopologicalSpace M›) :)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]
/-
**continuousSMul_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_iInf {ts' : ι -> TopologicalSpace X} (h : forall i, @Contin
uousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i)
参数：h : forall i, @ContinuousSMul M X _ _ (ts' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_sInf`：continuousSMul_sInf {ts : Set (TopologicalSpace X)}
 (h : forall t in ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf
 ts)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem continuousSMul_iInf {ts' : ι → TopologicalSpace X}
    (h : ∀ i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i) :=
  continuousSMul_sInf <| Set.forall_mem_range.mpr h

set_option linter.overlappingInstances false in
@[to_additive]
/-
**continuousSMul_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t
₁] [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `continuousSMul_iInf`：continuousSMul_iInf {ts' : ι -> TopologicalSpace X}
 (h : forall i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i,
 ts' i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
    [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section AddTorsor

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] [TopologicalSpace G]
variable [PreconnectedSpace G] [TopologicalSpace P] [ContinuousVAdd G P]

include G in
/-- An `AddTorsor` for a connected space is a connected space. This is not an instance because
it loops for a group as a torsor over itself. -/
/-
**AddTorsor.connectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `AddTorsor`。
形式化陈述：∀ (G : Type u_1) (P : Type u_2) [inst : AddGroup G] [inst_1 : AddTorsor G 
P] [inst_2 : TopologicalSpace G]   [PreconnectedSpace G] [inst_4 : TopologicalSp
ace P] [ContinuousVAdd G P], ConnectedSpace P
参数：G : Type u_1；P : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Equiv.range_eq_univ`：range_eq_univ (e : α ≃ β) : range e = univ
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : 
TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace Y
] [in…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
An `AddTorsor` for a connected space is a connected space. This is not an instan
ce because
it loops for a group as a torsor over itself.
-/
protected theorem AddTorsor.connectedSpace : ConnectedSpace P :=
  { isPreconnected_univ := by
      convert!
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G → P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ, Equiv.range_eq_univ]
    toNonempty := inferInstance }

end AddTorsor

