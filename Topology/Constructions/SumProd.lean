/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Separation.SeparatedNhds

/-!
# Disjoint unions and products of topological spaces

This file constructs sums (disjoint unions) and products of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

We also provide basic homeomorphisms, to show that sums and products are commutative, associative
and distributive (up to homeomorphism).

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union

-/

@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

/-
**instTopologicalSpaceSum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y
] : TopologicalSpace (X oplus Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂
/-
**instTopologicalSpaceProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace 
Y] : TopologicalSpace (X × Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

@[simp]
/-
**continuous_prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prodMk {f : X -> Y} {g : X -> Z} : (Continuous fun x => (f x, g
 x)) ↔ Continuous f ∧ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_inf_rng`：continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ 
: TopologicalSpace β} : Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Conti
nuous[t₁…
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
-/
theorem continuous_prodMk {f : X → Y} {g : X → Z} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  continuous_inf_rng.trans <| continuous_induced_rng.and continuous_induced_rng

@[continuity]
/-
**continuous_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Continuous (fun x ↦ (
f x).fst)
参数：f : X → Y × Z；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_prodMk`：continuous_prodMk {f : X -> Y} {g : X -> Z} : (Contin
uous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_fst : Continuous (@Prod.fst X Y) :=
  (continuous_prodMk.1 continuous_id).1

/-- Postcomposing `f` with `Prod.fst` is continuous -/
@[fun_prop]
/-
**Continuous.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Continuous fun x : X
 => (f x).1
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Postcomposing `f` with `Prod.fst` is continuous
-/
theorem Continuous.fst {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).1 :=
  continuous_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous -/
/-
**Continuous.fst'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Continuous fun x : X × 
Y => f x.fst
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Precomposing `f` with `Prod.fst` is continuous
-/
theorem Continuous.fst' {f : X → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.fst :=
  hf.comp continuous_fst
/-
**continuousAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
  continuous_fst.continuousAt

/-- Postcomposing `f` with `Prod.fst` is continuous at `x` -/
@[fun_prop]
/-
**ContinuousAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x) : Contin
uousAt (fun x : X => (f x).1) x
参数：hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p

--- 原说明 ---
Postcomposing `f` with `Prod.fst` is continuous at `x`
-/
theorem ContinuousAt.fst {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).1) x :=
  continuousAt_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous at `(x, y)` -/
/-
**ContinuousAt.fst'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.fst' {f : X -> Z} {x : X} {y : Y} (hf : ContinuousAt f x) : C
ontinuousAt (fun x : X × Y => f x.fst) (x, y)
参数：hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p

--- 原说明 ---
Precomposing `f` with `Prod.fst` is continuous at `(x, y)`
-/
theorem ContinuousAt.fst' {f : X → Z} {x : X} {y : Y} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X × Y => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst

/-- Precomposing `f` with `Prod.fst` is continuous at `x : X × Y` -/
/-
**ContinuousAt.fst''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.fst'' {f : X -> Z} {x : X × Y} (hf : ContinuousAt f x.fst) : 
ContinuousAt (fun x : X × Y => f x.fst) x
参数：hf : ContinuousAt f x.fst。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p

--- 原说明 ---
Precomposing `f` with `Prod.fst` is continuous at `x : X × Y`
-/
theorem ContinuousAt.fst'' {f : X → Z} {x : X × Y} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : X × Y => f x.fst) x :=
  hf.comp continuousAt_fst
/-
**Filter.Tendsto.fst_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.fst_nhds {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z} (h
 : Tendsto f l (𝓝 p)) : Tendsto (fun a => (f a).1) l (𝓝 <| p.1)
参数：h : Tendsto f l (𝓝 p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
-/
theorem Filter.Tendsto.fst_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).1) l (𝓝 <| p.1) :=
  continuousAt_fst.tendsto.comp h

@[continuity]
/-
**continuous_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Continuous (fun x ↦ (
f x).snd)
参数：f : X → Y × Z；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_prodMk`：continuous_prodMk {f : X -> Y} {g : X -> Z} : (Contin
uous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_snd : Continuous (@Prod.snd X Y) :=
  (continuous_prodMk.1 continuous_id).2

/-- Postcomposing `f` with `Prod.snd` is continuous -/
@[fun_prop]
/-
**Continuous.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Continuous fun x : X
 => (f x).2
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
Postcomposing `f` with `Prod.snd` is continuous
-/
theorem Continuous.snd {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).2 :=
  continuous_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous -/
/-
**Continuous.snd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Continuous fun x : X × 
Y => f x.snd
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
Precomposing `f` with `Prod.snd` is continuous
-/
theorem Continuous.snd' {f : Y → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.snd :=
  hf.comp continuous_snd
/-
**continuousAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
  continuous_snd.continuousAt

/-- Postcomposing `f` with `Prod.snd` is continuous at `x` -/
@[fun_prop]
/-
**ContinuousAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : ContinuousAt f x) : Contin
uousAt (fun x : X => (f x).2) x
参数：hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p

--- 原说明 ---
Postcomposing `f` with `Prod.snd` is continuous at `x`
-/
theorem ContinuousAt.snd {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).2) x :=
  continuousAt_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous at `(x, y)` -/
/-
**ContinuousAt.snd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.snd' {f : Y -> Z} {x : X} {y : Y} (hf : ContinuousAt f y) : C
ontinuousAt (fun x : X × Y => f x.snd) (x, y)
参数：hf : ContinuousAt f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p

--- 原说明 ---
Precomposing `f` with `Prod.snd` is continuous at `(x, y)`
-/
theorem ContinuousAt.snd' {f : Y → Z} {x : X} {y : Y} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : X × Y => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd

/-- Precomposing `f` with `Prod.snd` is continuous at `x : X × Y` -/
/-
**ContinuousAt.snd''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.snd'' {f : Y -> Z} {x : X × Y} (hf : ContinuousAt f x.snd) : 
ContinuousAt (fun x : X × Y => f x.snd) x
参数：hf : ContinuousAt f x.snd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p

--- 原说明 ---
Precomposing `f` with `Prod.snd` is continuous at `x : X × Y`
-/
theorem ContinuousAt.snd'' {f : Y → Z} {x : X × Y} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : X × Y => f x.snd) x :=
  hf.comp continuousAt_snd
/-
**Filter.Tendsto.snd_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.snd_nhds {X} {l : Filter X} {f : X -> Y × Z} {p : Y × Z} (h
 : Tendsto f l (𝓝 p)) : Tendsto (fun a => (f a).2) l (𝓝 <| p.2)
参数：h : Tendsto f l (𝓝 p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
-/
theorem Filter.Tendsto.snd_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).2) l (𝓝 <| p.2) :=
  continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]
/-
**Continuous.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Continuous f) (hg : Cont
inuous g) : Continuous fun x => (f x, g x)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_prodMk`：continuous_prodMk {f : X -> Y} {g : X -> Z} : (Contin
uous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g
-/
theorem Continuous.prodMk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_prodMk.2 ⟨hf, hg⟩

@[continuity]
/-
**Continuous.prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.prodMk_right (x : X) : Continuous fun y : Y => (x, y)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem Continuous.prodMk_right (x : X) : Continuous fun y : Y => (x, y) := by fun_prop

@[continuity]
/-
**Continuous.prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.prodMk_left (y : Y) : Continuous fun x : X => (x, y)
参数：y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem Continuous.prodMk_left (y : Y) : Continuous fun x : X => (x, y) := by fun_prop

@[continuity, fun_prop]
/-
**continuous_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_diag : Continuous (Function.diag : X -> X × X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_diag : Continuous (Function.diag : X → X × X) :=
  continuous_id.prodMk continuous_id

/-- If `f x y` is continuous in `x` for all `y ∈ s`,
then the set of `x` such that `f x` maps `s` to `t` is closed. -/
/-
**IsClosed.setOfPred_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.setOfPred_mapsTo {α : Type*} {f : X -> α -> Z} {s : Set α} {t : S
et Z} (ht : IsClosed t) (hf : forall a in s, Continuous (f · a)) : IsClosed {x |
 MapsTo (f x) s t}
参数：ht : IsClosed t；hf : forall a in s, Continuous (f · a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)

--- 原说明 ---
If `f x y` is continuous in `x` for all `y ∈ s`,
then the set of `x` such that `f x` maps `s` to `t` is closed.
-/
lemma IsClosed.setOfPred_mapsTo {α : Type*} {f : X → α → Z} {s : Set α} {t : Set Z}
    (ht : IsClosed t)
    (hf : ∀ a ∈ s, Continuous (f · a)) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, ofPred_forall] using! isClosed_biInter fun y hy ↦ ht.preimage (hf y hy)

@[deprecated (since := "2026-07-09")]
alias IsClosed.setOf_mapsTo := IsClosed.setOfPred_mapsTo
/-
**Continuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) : Con
tinuous (g ∘ f)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem Continuous.comp₂ {g : X × Y → Z} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) : Continuous fun w => g (e w, f w) :=
  hg.comp <| he.prodMk hf
/-
**Continuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) : Con
tinuous (g ∘ f)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem Continuous.comp₃ {g : X × Y × Z → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) :
    Continuous fun w => g (e w, f w, k w) :=
  hg.comp₂ he <| hf.prodMk hk
/-
**Continuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) : Con
tinuous (g ∘ f)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem Continuous.comp₄ {g : X × Y × Z × ζ → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) {l : W → ζ}
    (hl : Continuous l) : Continuous fun w => g (e w, f w, k w, l w) :=
  hg.comp₃ he hf <| hk.prodMk hl

@[continuity, fun_prop]
/-
**Continuous.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : Continuous f) (hg : Con
tinuous g) : Continuous (Prod.map f g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
-/
theorem Continuous.prodMap {f : Z → X} {g : W → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Prod.map f g) :=
  hf.fst'.prodMk hg.snd'

/-- A version of `continuous_inf_dom_left` for binary functions -/
/-
**continuous_inf_dom_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpac
e β} : Continuous[t₁, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
A version of `continuous_inf_dom_left` for binary functions
-/
theorem continuous_inf_dom_left₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta1; haveI := tb1; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_inf_dom_right` for binary functions -/
/-
**continuous_inf_dom_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpa
ce β} : Continuous[t₂, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
A version of `continuous_inf_dom_right` for binary functions
-/
theorem continuous_inf_dom_right₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta2; haveI := tb2; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_sInf_dom` for binary functions -/
/-
**continuous_sInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace
 β} {t : TopologicalSpace α} (h₁ : t in t₁) : Continuous[t, t₂] f -> Continuous[
sInf t₁, t₂] f
参数：TopologicalSpace α；h₁ : t in t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
A version of `continuous_sInf_dom` for binary functions
-/
theorem continuous_sInf_dom₂ {X Y Z} {f : X → Y → Z} {tas : Set (TopologicalSpace X)}
    {tbs : Set (TopologicalSpace Y)} {tX : TopologicalSpace X} {tY : TopologicalSpace Y}
    {tc : TopologicalSpace Z} (hX : tX ∈ tas) (hY : tY ∈ tbs)
    (hf : Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id
/-
**Filter.Eventually.prod_inl_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.prod_inl_nhds {p : X -> Prop} {x : X} (h : forallᶠ x in 
𝓝 x, p x) (y : Y) : forallᶠ x in 𝓝 (x, y), p (x : X × Y).1
参数：h : forallᶠ x in 𝓝 x, p x；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
-/
theorem Filter.Eventually.prod_inl_nhds {p : X → Prop} {x : X} (h : ∀ᶠ x in 𝓝 x, p x) (y : Y) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).1 :=
  continuousAt_fst h
/-
**Filter.Eventually.prod_inr_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.prod_inr_nhds {p : Y -> Prop} {y : Y} (h : forallᶠ x in 
𝓝 y, p x) (x : X) : forallᶠ x in 𝓝 (x, y), p (x : X × Y).2
参数：h : forallᶠ x in 𝓝 y, p x；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
-/
theorem Filter.Eventually.prod_inr_nhds {p : Y → Prop} {y : Y} (h : ∀ᶠ x in 𝓝 y, p x) (x : X) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).2 :=
  continuousAt_snd h
/-
**Filter.Eventually.prodMk_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.prodMk_nhds {px : X -> Prop} {x} (hx : forallᶠ x in 𝓝 x,
 px x) {py : Y -> Prop} {y} (hy : forallᶠ y in 𝓝 y, py y) : forallᶠ p in 𝓝 (x, y
), px (p : X × Y).1 ∧ py p.2
参数：hx : forallᶠ x in 𝓝 x, px x；hy : forallᶠ y in 𝓝 y, py y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.prod_inl_nhds`：Filter.Eventually.prod_inl_nhds {p : X 
-> Prop} {x : X} (h : forallᶠ x in 𝓝 x, p x) (y : Y) : forallᶠ x in 𝓝 (x, y), p 
(x : X × Y).1
· 使用定理 `Filter.Eventually.prod_inr_nhds`：Filter.Eventually.prod_inr_nhds {p : Y 
-> Prop} {y : Y} (h : forallᶠ x in 𝓝 y, p x) (x : X) : forallᶠ x in 𝓝 (x, y), p 
(x : X × Y).2
-/
theorem Filter.Eventually.prodMk_nhds {px : X → Prop} {x} (hx : ∀ᶠ x in 𝓝 x, px x) {py : Y → Prop}
    {y} (hy : ∀ᶠ y in 𝓝 y, py y) : ∀ᶠ p in 𝓝 (x, y), px (p : X × Y).1 ∧ py p.2 :=
  (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

@[fun_prop]
/-
**continuous_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_swap : Continuous (Prod.swap : X × Y -> Y × X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem continuous_swap : Continuous (Prod.swap : X × Y → Y × X) :=
  continuous_snd.prodMk continuous_fst
/-
**isClosedMap_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_swap : IsClosedMap (Prod.swap : X × Y -> Y × X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_swap_eq_preimage_swap`：image_swap_eq_preimage_swap : image (@P
rod.swap α β) = preimage Prod.swap
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
lemma isClosedMap_swap : IsClosedMap (Prod.swap : X × Y → Y × X) := fun s hs ↦ by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap
/-
**Continuous.uncurry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.uncurry_left {f : X -> Y -> Z} (x : X) (h : Continuous (uncurry
 f)) : Continuous (f x)
参数：x : X；h : Continuous (uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
theorem Continuous.uncurry_left {f : X → Y → Z} (x : X) (h : Continuous (uncurry f)) :
    Continuous (f x) :=
  h.comp (.prodMk_right _)
/-
**Continuous.uncurry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.uncurry_right {f : X -> Y -> Z} (y : Y) (h : Continuous (uncurr
y f)) : Continuous fun a => f a y
参数：y : Y；h : Continuous (uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
-/
theorem Continuous.uncurry_right {f : X → Y → Z} (y : Y) (h : Continuous (uncurry f)) :
    Continuous fun a => f a y :=
  h.comp (.prodMk_left _)
/-
**continuous_curry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_curry {g : X × Y -> Z} (x : X) (h : Continuous g) : Continuous 
(curry g x)
参数：x : X；h : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.uncurry_left`：Continuous.uncurry_left {f : X -> Y -> Z} (x : 
X) (h : Continuous (uncurry f)) : Continuous (f x)
-/
theorem continuous_curry {g : X × Y → Z} (x : X) (h : Continuous g) : Continuous (curry g x) :=
  Continuous.uncurry_left x h
/-
**IsOpen.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOp
en (s ×ˢ t)
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

-- Porting note: Lean fails to find `t₁` and `t₂` by unification
/-
**nhds_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq_inf`：prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g =
 f.comap Prod.fst ⊓ g.comap Prod.snd
· 使用定理 `instTopologicalSpaceProd.eq_1`：∀ {X : Type u} {Y : Type v} [t₁ : Topolog
icalSpace X] [t₂ : TopologicalSpace Y],   instTopologicalSpaceProd = Topological
Space.induced Prod.…
· 使用定理 `nhds_inf`：nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} : @nhds α (t₁ ⊓ 
t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
-/
theorem nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y := by
  rw [prod_eq_inf, instTopologicalSpaceProd, nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _), nhds_induced, nhds_induced]
/-
**nhdsWithin_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) : 𝓝[s ×ˢ t] (x,
 y) = 𝓝[s] x ×ˢ 𝓝[t] y
参数：x : X；y : Y；s : Set X；t : Set Y。
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
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) :
    𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y := by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]
/-
**Prod.instNeBotNhdsWithinIio** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instNeBotNhdsWithinIio [Preorder X] [Preorder Y] {x : X × Y} [hx₁ : (
𝓝[<] x.1).NeBot] [hx₂ : (𝓝[<] x.2).NeBot] : (𝓝[<] x).NeBot
参数：𝓝[<] x.1；𝓝[<] x.2。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Filter.NeBot.prod`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : F
ilter β}, f.NeBot → g.NeBot → (f ×ˢ g).NeBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance Prod.instNeBotNhdsWithinIio [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[<] x.1).NeBot] [hx₂ : (𝓝[<] x.2).NeBot] : (𝓝[<] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
  exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ ↦ Prod.lt_iff.2 <| .inl ⟨h₁, h₂.le⟩
/-
**Prod.instNeBotNhdsWithinIoi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instNeBotNhdsWithinIoi [Preorder X] [Preorder Y] {x : X × Y} [hx₁ : (
𝓝[>] x.1).NeBot] [hx₂ : (𝓝[>] x.2).NeBot] : (𝓝[>] x).NeBot
参数：𝓝[>] x.1；𝓝[>] x.2。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Filter.NeBot.prod`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : F
ilter β}, f.NeBot → g.NeBot → (f ×ˢ g).NeBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance Prod.instNeBotNhdsWithinIoi [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[>] x.1).NeBot] [hx₂ : (𝓝[>] x.2).NeBot] : (𝓝[>] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
  exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ ↦ Prod.lt_iff.2 <| .inl ⟨h₁, h₂.le⟩
/-
**mem_nhds_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} : s in 𝓝 (x, y) ↔ exis
ts u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
参数：X × Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u ∈ 𝓝 x, ∃ v ∈ 𝓝 y, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]
/-
**mem_nhdsWithin_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty
 : Set Y} : s in 𝓝[tx ×ˢ ty] (x, y) ↔ exists u in 𝓝[tx] x, exists v in 𝓝[ty] y, 
u ×ˢ v subseteq s
参数：X × Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y} :
    s ∈ 𝓝[tx ×ˢ ty] (x, y) ↔ ∃ u ∈ 𝓝[tx] x, ∃ v ∈ 𝓝[ty] y, u ×ˢ v ⊆ s := by
  rw [nhdsWithin_prod_eq, mem_prod_iff]
/-
**Filter.HasBasis.prod_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX -> Prop} {py : ιY -> Pr
op} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis p
x sx) (hy : (𝓝 y).HasBasis py sy) : (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i
.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2
参数：hx : (𝓝 x).HasBasis px sx；hy : (𝓝 y).HasBasis py sy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
-/
theorem Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX → Prop} {py : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis px sx)
    (hy : (𝓝 y).HasBasis py sy) :
    (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2 := by
  rw [nhds_prod_eq]
  exact hx.prod hy
/-
**Filter.HasBasis.prod_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX -> Prop} {pY : ιY -> P
rop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX
 sx) (hy : (𝓝 p.2).HasBasis pY sy) : (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧
 pY i.2) fun i => sx i.1 ×ˢ sy i.2
参数：hx : (𝓝 p.1).HasBasis pX sx；hy : (𝓝 p.2).HasBasis pY sy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
-/
theorem Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX → Prop} {pY : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX sx)
    (hy : (𝓝 p.2).HasBasis pY sy) :
    (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧ pY i.2) fun i => sx i.1 ×ˢ sy i.2 :=
  hx.prod_nhds hy
/-
**mem_nhds_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} : s in 𝓝 (x, y) ↔ exi
sts u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v subseteq s
参数：X × Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧ u ×ˢ v ⊆ s :=
  ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans <| by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]
/-
**Prod.tendsto_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X} (p : Y × Z) : Tends
to seq f (𝓝 p) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => 
(seq n).snd) f (𝓝 p.snd)
参数：seq : X -> Y × Z；p : Y × Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.tendsto_prod_iff'`：tendsto_prod_iff' {g' : Filter γ} {s : α -> β 
× γ} : Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n =
> (s n).2) f g…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prod.tendsto_iff {X} (seq : X → Y × Z) {f : Filter X} (p : Y × Z) :
    Tendsto seq f (𝓝 p) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd) := by
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq, nhds_discrete X, nhds_discrete Y, prod_pure_pure]
/-
**prod_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} : s ×ˢ t in 𝓝 (x
, y) ↔ s in 𝓝 x ∧ t in 𝓝 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_mem_prod_iff`：prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t
 in f ×ˢ g ↔ s in f ∧ t in g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} :
    s ×ˢ t ∈ 𝓝 (x, y) ↔ s ∈ 𝓝 x ∧ t ∈ 𝓝 y := by rw [nhds_prod_eq, prod_mem_prod_iff]
/-
**prod_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s in 𝓝 x) (hy 
: t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
参数：hx : s in 𝓝 x；hy : t in 𝓝 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `prod_mem_nhds_iff`：prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y 
: Y} : s ×ˢ t in 𝓝 (x, y) ↔ s in 𝓝 x ∧ t in 𝓝 y
-/
theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s ∈ 𝓝 x) (hy : t ∈ 𝓝 y) :
    s ×ˢ t ∈ 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩
/-
**isOpen_setOfPred_disjoint_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1
) (𝓝 p.2) }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_prod_iff'`：mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)}
 : s in 𝓝 (x, y) ↔ exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v su
bseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem isOpen_setOfPred_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_ofPred_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_disjoint_nhds_nhds := isOpen_setOfPred_disjoint_nhds_nhds
/-
**Filter.Eventually.prod_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.prod_nhds {p : X -> Prop} {q : Y -> Prop} {x : X} {y : Y
} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in 𝓝 y, q y) : forallᶠ z : X × Y 
in 𝓝 (x, y), p z.1 ∧ q z.2
参数：hx : forallᶠ x in 𝓝 x, p x；hy : forallᶠ y in 𝓝 y, q y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
-/
theorem Filter.Eventually.prod_nhds {p : X → Prop} {q : Y → Prop} {x : X} {y : Y}
    (hx : ∀ᶠ x in 𝓝 x, p x) (hy : ∀ᶠ y in 𝓝 y, q y) : ∀ᶠ z : X × Y in 𝓝 (x, y), p z.1 ∧ q z.2 :=
  prod_mem_nhds hx hy
/-
**Filter.EventuallyEq.prodMap_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.prodMap_nhds {α β : Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y
 -> β} {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) (hg : g₁ =ᶠ[𝓝 y] g₂) : Prod.map f₁ g
₁ =ᶠ[𝓝 (x, y)] Prod.map f₂ g₂
参数：hf : f₁ =ᶠ[𝓝 x] f₂；hg : g₁ =ᶠ[𝓝 y] g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
-/
theorem Filter.EventuallyEq.prodMap_nhds {α β : Type*} {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) (hg : g₁ =ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ =ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg
/-
**Filter.EventuallyLE.prodMap_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.prodMap_nhds {α β : Type*} [LE α] [LE β] {f₁ f₂ : X ->
 α} {g₁ g₂ : Y -> β} {x : X} {y : Y} (hf : f₁ <=ᶠ[𝓝 x] f₂) (hg : g₁ <=ᶠ[𝓝 y] g₂)
 : Prod.map f₁ g₁ <=ᶠ[𝓝 (x, y)] Prod.map f₂ g₂
参数：hf : f₁ <=ᶠ[𝓝 x] f₂；hg : g₁ <=ᶠ[𝓝 y] g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.EventuallyLE.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} [inst : LE γ] [inst_1 : LE δ] {la : Filter α}   {fa ga : α → 
γ},   fa ≤ᶠ[la] g…
-/
theorem Filter.EventuallyLE.prodMap_nhds {α β : Type*} [LE α] [LE β] {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ ≤ᶠ[𝓝 x] f₂) (hg : g₁ ≤ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ ≤ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg
/-
**nhds_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
-/
theorem nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq]
/-
**Filter.Tendsto.prodMk_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ -> X
} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) : Tendsto (f
un c => (mx c, my c)) f (𝓝 (x, y))
参数：hx : Tendsto mx f (𝓝 x)；hy : Tendsto my f (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
theorem Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y}
    (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) :
    Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y)) := by
  rw [nhds_prod_eq]
  exact hx.prodMk hy
/-
**Filter.Tendsto.prodMap_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.prodMap_nhds {x : X} {y : Y} {z : Z} {w : W} {f : X -> Y} {
g : Z -> W} (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Tendsto g (𝓝 z) (𝓝 w)) : Tendsto 
(Prod.map f g) (𝓝 (x, z)) (𝓝 (y, w))
参数：hf : Tendsto f (𝓝 x) (𝓝 y)；hg : Tendsto g (𝓝 z) (𝓝 w)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
-/
theorem Filter.Tendsto.prodMap_nhds {x : X} {y : Y} {z : Z} {w : W} {f : X → Y} {g : Z → W}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Tendsto g (𝓝 z) (𝓝 w)) :
    Tendsto (Prod.map f g) (𝓝 (x, z)) (𝓝 (y, w)) := by
  rw [nhds_prod_eq, nhds_prod_eq]
  exact hf.prodMap hg
/-
**Filter.Eventually.curry_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.curry_nhds {p : X × Y -> Prop} {x : X} {y : Y} (h : fora
llᶠ x in 𝓝 (x, y), p x) : forallᶠ x' in 𝓝 x, forallᶠ y' in 𝓝 y, p (x', y')
参数：h : forallᶠ x in 𝓝 (x, y), p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
-/
theorem Filter.Eventually.curry_nhds {p : X × Y → Prop} {x : X} {y : Y}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]
/-
**ContinuousAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : X} (hf : ContinuousAt f
 x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem ContinuousAt.prodMk {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prodMk_nhds hg
/-
**ContinuousAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p : X × Y} (hf : Continuou
sAt f p.fst) (hg : ContinuousAt g p.snd) : ContinuousAt (Prod.map f g) p
参数：hf : ContinuousAt f p.fst；hg : ContinuousAt g p.snd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `ContinuousAt.fst''`：ContinuousAt.fst'' {f : X -> Z} {x : X × Y} (hf : Co
ntinuousAt f x.fst) : ContinuousAt (fun x : X × Y => f x.fst) x
· 使用定理 `ContinuousAt.snd''`：ContinuousAt.snd'' {f : Y -> Z} {x : X × Y} (hf : Co
ntinuousAt f x.snd) : ContinuousAt (fun x : X × Y => f x.snd) x
-/
theorem ContinuousAt.prodMap {f : X → Z} {g : Y → W} {p : X × Y} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (Prod.map f g) p :=
  hf.fst''.prodMk hg.snd''

/-- A version of `ContinuousAt.prodMap` that avoids `Prod.fst`/`Prod.snd`
by assuming that the point is `(x, y)`. -/
/-
**ContinuousAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.prodMap' {f : X -> Z} {g : Y -> W} {x : X} {y : Y} (hf : Cont
inuousAt f x) (hg : ContinuousAt g y) : ContinuousAt (Prod.map f g) (x, y)
参数：hf : ContinuousAt f x；hg : ContinuousAt g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.prodMap`：ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p 
: X × Y} (hf : ContinuousAt f p.fst) (hg : ContinuousAt g p.snd) : ContinuousAt 
(Prod.map …

--- 原说明 ---
A version of `ContinuousAt.prodMap` that avoids `Prod.fst`/`Prod.snd`
by assuming that the point is `(x, y)`.
-/
theorem ContinuousAt.prodMap' {f : X → Z} {g : Y → W} {x : X} {y : Y} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (Prod.map f g) (x, y) :=
  hf.prodMap hg

@[simp]
/-
**continuousAt_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_prodMap_iff {f : X -> Z} {g : Y -> W} {x : X} {y : Y} : Conti
nuousAt (Prod.map f g) (x, y) ↔ ContinuousAt f x ∧ ContinuousAt g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.comap_prodMap_prod`：comap_prodMap_prod (f : α -> β) (g : γ -> δ) 
(lb : Filter β) (ld : Filter δ) : comap (Prod.map f g) (lb ×ˢ ld) = comap f lb ×
ˢ comap g ld
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_prodMap_iff {f : X → Z} {g : Y → W} {x : X} {y : Y} :
    ContinuousAt (Prod.map f g) (x, y) ↔ ContinuousAt f x ∧ ContinuousAt g y := by
  simp [ContinuousAt, nhds_prod_eq, tendsto_iff_comap, comap_prodMap_prod]

@[simp]
/-
**continuous_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prodMap_iff [Nonempty Z] [Nonempty W] {f : Z -> X} {g : W -> Y}
 : Continuous (Prod.map f g) ↔ Continuous f ∧ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_prodMap_iff [Nonempty Z] [Nonempty W] {f : Z → X} {g : W → Y} :
    Continuous (Prod.map f g) ↔ Continuous f ∧ Continuous g := by
  simp [continuous_iff_continuousAt, forall_and]
/-
**ContinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {x : 
X} {g : Y → Z},   ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f)
 x
参数：f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem ContinuousAt.comp₂ {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X}
    (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh : ContinuousAt h x) :
    ContinuousAt (fun x ↦ f (g x, h x)) x :=
  ContinuousAt.comp hf (hg.prodMk hh)
/-
**ContinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {x : 
X} {g : Y → Z},   ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f)
 x
参数：f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem ContinuousAt.comp₂_of_eq {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X} {y : Y × Z}
    (hf : ContinuousAt f y) (hg : ContinuousAt g x) (hh : ContinuousAt h x) (e : (g x, h x) = y) :
    ContinuousAt (fun x ↦ f (g x, h x)) x := by
  rw [← e] at hf
  exact hf.comp₂ hg hh

/-- Continuous functions on products are continuous in their first argument -/
/-
**Continuous.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.curry_left {f : X × Y -> Z} (hf : Continuous f) {y : Y} : Conti
nuous fun x => f (x, y)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)

--- 原说明 ---
Continuous functions on products are continuous in their first argument
-/
theorem Continuous.curry_left {f : X × Y → Z} (hf : Continuous f) {y : Y} :
    Continuous fun x ↦ f (x, y) :=
  hf.comp (.prodMk_left _)
alias Continuous.along_fst := Continuous.curry_left

/-- Continuous functions on products are continuous in their second argument -/
/-
**Continuous.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.curry_right {f : X × Y -> Z} (hf : Continuous f) {x : X} : Cont
inuous fun y => f (x, y)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)

--- 原说明 ---
Continuous functions on products are continuous in their second argument
-/
theorem Continuous.curry_right {f : X × Y → Z} (hf : Continuous f) {x : X} :
    Continuous fun y ↦ f (x, y) :=
  hf.comp (.prodMk_right _)
alias Continuous.along_snd := Continuous.curry_right

-- todo: prove a version of `generateFrom_union` with `image2 (∩) s t` in the LHS and use it here
/-
**prod_generateFrom_generateFrom_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_generateFrom_generateFrom_eq {X Y : Type*} {s : Set (Set X)} {t : Set
 (Set Y)} (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) : @instTopologicalSpaceProd X Y 
(generateFrom s) (generateFrom t) = generateFrom (image2 (· ×ˢ ·) s t)
参数：Set X；Set Y；hs : ⋃₀ s = univ；ht : ⋃₀ t = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
-/
theorem prod_generateFrom_generateFrom_eq {X Y : Type*} {s : Set (Set X)} {t : Set (Set Y)}
    (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
    @instTopologicalSpaceProd X Y (generateFrom s) (generateFrom t) =
      generateFrom (image2 (· ×ˢ ·) s t) :=
  let G := generateFrom (image2 (· ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun u hu =>
          have : ⋃ v ∈ t, u ×ˢ v = Prod.fst ⁻¹' u := by
            simp_rw [← prod_iUnion, ← sUnion_eq_biUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact
              isOpen_iUnion fun v =>
                isOpen_iUnion fun hv => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun v hv =>
          have : ⋃ u ∈ s, u ×ˢ v = Prod.snd ⁻¹' v := by
            simp_rw [← iUnion_prod_const, ← sUnion_eq_biUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact
              isOpen_iUnion fun u =>
                isOpen_iUnion fun hu => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩))
/-
**prod_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_eq_generateFrom : instTopologicalSpaceProd = generateFrom { g | exist
s (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
-/
theorem prod_eq_generateFrom :
    instTopologicalSpaceProd =
      generateFrom { g | ∃ (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (coinduced_le_iff_le_induced.mp fun U hU ↦
        .basic _ ⟨U, univ, hU, isOpen_univ, prod_univ.symm⟩)
      (coinduced_le_iff_le_induced.mp fun U hU ↦
        .basic _ ⟨univ, U, isOpen_univ, hU, univ_prod.symm⟩))

-- TODO: align with `mem_nhds_prod_iff'`
/-
**isOpen_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_prod_iff {s : Set (X × Y)} : IsOpen s ↔ forall a b, (a, b) in s -> 
exists u v, IsOpen u ∧ IsOpen v ∧ a in u ∧ b in v ∧ u ×ˢ v subseteq s
参数：X × Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  isOpen_iff_mem_nhds.trans <| by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

/-- A product of induced topologies is induced by the product map -/
/-
**prod_induced_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_induced_induced {X Z} (f : X -> Y) (g : Z -> W) : @instTopologicalSpa
ceProd X Z (induced f ‹_›) (induced g ‹_›) = induced (fun p => (f p.1, g p.2)) i
nstTopologicalSpaceProd
参数：f : X -> Y；g : Z -> W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)

--- 原说明 ---
A product of induced topologies is induced by the product map
-/
theorem prod_induced_induced {X Z} (f : X → Y) (g : Z → W) :
    @instTopologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instTopologicalSpaceProd := by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
/-
**exists_nhds_square** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_square {s : Set (X × X)} {x : X} (hx : s in 𝓝 (x, x)) : exists
 U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq s
参数：X × X；hx : s in 𝓝 (x, x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborho
od
  that is a subset of `s`.
-/
theorem exists_nhds_square {s : Set (X × X)} {x : X} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

/-- `Prod.fst` maps neighborhood of `x : X × Y` within the section `Prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
/-
**map_fst_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 
𝓝 x.1
参数：x : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
`Prod.fst` maps neighborhood of `x : X × Y` within the section `Prod.snd ⁻¹' {x.
2}`
to `𝓝 x.1`.
-/
theorem map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
/-
**map_fst_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1
参数：x : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_fst_nhdsWithin`：map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Pro
d.snd ⁻¹' {x.2}] x) = 𝓝 x.1
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuousAt_fst <| (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
/-
**isOpenMap_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_fst : IsOpenMap (@Prod.fst X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_iff_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X),
 nhds (f x)…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `map_fst_nhds`：map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1

--- 原说明 ---
The first projection in a product of topological spaces sends open sets to open 
sets.
-/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

/-- `Prod.snd` maps neighborhood of `x : X × Y` within the section `Prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
/-
**map_snd_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 
𝓝 x.2
参数：x : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
`Prod.snd` maps neighborhood of `x : X × Y` within the section `Prod.fst ⁻¹' {x.
1}`
to `𝓝 x.2`.
-/
theorem map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_ofPred_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
/-
**map_snd_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2
参数：x : X × Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_snd_nhdsWithin`：map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Pro
d.fst ⁻¹' {x.1}] x) = 𝓝 x.2
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuousAt_snd <| (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
/-
**isOpenMap_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_snd : IsOpenMap (@Prod.snd X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_iff_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X),
 nhds (f x)…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `map_snd_nhds`：map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2

--- 原说明 ---
The second projection in a product of topological spaces sends open sets to open
 sets.
-/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
/-
**isOpen_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_prod_iff' {s : Set X} {t : Set Y} : IsOpen (s ×ˢ t) ↔ IsOpen s ∧ Is
Open t ∨ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.prod_nonempty_iff`：prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempt
y ∧ t.Nonempty
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isOpenMap_fst`：isOpenMap_fst : IsOpenMap (@Prod.fst X Y)
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpenMap_snd`：isOpenMap_snd : IsOpenMap (@Prod.snd X Y)
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
A product set is open in a product space if and only if each factor is open, or 
one of them is
empty
-/
theorem isOpen_prod_iff' {s : Set X} {t : Set Y} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
      · simpa only [snd_image_prod st.1 t] using isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H
      exact H.1.prod H.2
/-
**isOpenQuotientMap_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenQuotientMap_fst [Nonempty Y] : IsOpenQuotientMap (Prod.fst : X × Y -
> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `isOpenMap_fst`：isOpenMap_fst : IsOpenMap (@Prod.fst X Y)
-/
theorem isOpenQuotientMap_fst [Nonempty Y] : IsOpenQuotientMap (Prod.fst : X × Y → X) :=
  ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩
/-
**isOpenQuotientMap_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenQuotientMap_snd [Nonempty X] : IsOpenQuotientMap (Prod.snd : X × Y -
> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `isOpenMap_snd`：isOpenMap_snd : IsOpenMap (@Prod.snd X Y)
-/
theorem isOpenQuotientMap_snd [Nonempty X] : IsOpenQuotientMap (Prod.snd : X × Y → Y) :=
  ⟨Prod.snd_surjective, continuous_snd, isOpenMap_snd⟩
/-
**isQuotientMap_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientMap_fst [Nonempty Y] : IsQuotientMap (Prod.fst : X × Y -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `isOpenQuotientMap_fst`：isOpenQuotientMap_fst [Nonempty Y] : IsOpenQuotie
ntMap (Prod.fst : X × Y -> X)
-/
theorem isQuotientMap_fst [Nonempty Y] : IsQuotientMap (Prod.fst : X × Y → X) :=
  isOpenQuotientMap_fst.isQuotientMap
/-
**isQuotientMap_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientMap_snd [Nonempty X] : IsQuotientMap (Prod.snd : X × Y -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `isOpenQuotientMap_snd`：isOpenQuotientMap_snd [Nonempty X] : IsOpenQuotie
ntMap (Prod.snd : X × Y -> Y)
-/
theorem isQuotientMap_snd [Nonempty X] : IsQuotientMap (Prod.snd : X × Y → Y) :=
  isOpenQuotientMap_snd.isQuotientMap
/-
**closure_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ 
closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]
/-
**interior_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s 
×ˢ interior t
参数：s : Set X；t : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]
/-
**frontier_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_prod_eq (s : Set X) (t : Set Y) : frontier (s ×ˢ t) = closure s ×
ˢ frontier t union frontier s ×ˢ closure t
参数：s : Set X；t : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
· 使用定理 `interior_prod_eq`：interior_prod_eq (s : Set X) (t : Set Y) : interior (s
 ×ˢ t) = interior s ×ˢ interior t
· 使用定理 `Set.prod_sdiff_prod`：prod_sdiff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁)
 union (s \ s₁) ×ˢ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_prod_eq (s : Set X) (t : Set Y) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_sdiff_prod]

@[simp]
/-
**frontier_prod_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_prod_univ_eq (s : Set X) : frontier (s ×ˢ (univ : Set Y)) = front
ier s ×ˢ univ
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_prod_eq`：frontier_prod_eq (s : Set X) (t : Set Y) : frontier (s
 ×ˢ t) = closure s ×ˢ frontier t union frontier s ×ˢ closure t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `frontier_univ`：frontier_univ : frontier (univ : Set X) = ∅
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_prod_univ_eq (s : Set X) :
    frontier (s ×ˢ (univ : Set Y)) = frontier s ×ˢ univ := by
  simp [frontier_prod_eq]

@[simp]
/-
**frontier_univ_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_univ_prod_eq (s : Set Y) : frontier ((univ : Set X) ×ˢ s) = univ 
×ˢ frontier s
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_prod_eq`：frontier_prod_eq (s : Set X) (t : Set Y) : frontier (s
 ×ˢ t) = closure s ×ˢ frontier t union frontier s ×ˢ closure t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `frontier_univ`：frontier_univ : frontier (univ : Set X) = ∅
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_univ_prod_eq (s : Set Y) :
    frontier ((univ : Set X) ×ˢ s) = univ ×ˢ frontier s := by
  simp [frontier_prod_eq]

/-- The hypotheses on `f` are slightly weaker here compared to `mem_map_closure₂`. That
lemma requires `f` to be jointly continuous, whereas here we only require continuity in each
variable separately. -/
/-
**map_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_closure {t : Set Y} (hf : Continuous f) (hx : x in closure s) (ht 
: MapsTo f s t) : f x in closure t
参数：hf : Continuous f；hx : x in closure s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …

--- 原说明 ---
The hypotheses on `f` are slightly weaker here compared to `mem_map_closure₂`. T
hat
lemma requires `f` to be jointly continuous, whereas here we only require contin
uity in each
variable separately.
-/
theorem map_mem_closure₂' {f : X → Y → Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf₁ : ∀ x, Continuous (f x)) (hf₂ : ∀ y, Continuous (f · y))
    (hx : x ∈ closure s) (hy : y ∈ closure t) (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) :
    f x y ∈ closure u := by
  rw [← isClosed_closure.closure_eq]
  apply map_mem_closure (hf₁ x) hy fun b hb ↦ ?_
  apply map_mem_closure (hf₂ b) hx fun a ha ↦ h a ha b hb
/-
**map_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_closure {t : Set Y} (hf : Continuous f) (hx : x in closure s) (ht 
: MapsTo f s t) : f x in closure t
参数：hf : Continuous f；hx : x in closure s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
-/
theorem map_mem_closure₂ {f : X → Y → Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf : Continuous (uncurry f)) (hx : x ∈ closure s) (hy : y ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f x y ∈ closure u :=
  have H₁ : (x, y) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁
/-
**IsClosed.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed 
s₂) : IsClosed (s₁ ×ˢ s₂)
参数：h₁ : IsClosed s₁；h₂ : IsClosed s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_isClosed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
/-
**Dense.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (
s ×ˢ t)
参数：hs : Dense s；ht : Dense t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_prod_eq`：closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ
 t) = closure s ×ˢ closure t

--- 原说明 ---
The product of two dense sets is a dense set.
-/
theorem Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

/-- If `f` and `g` are maps with dense range, then `Prod.map f g` has dense range. -/
/-
**DenseRange.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι -> Y} {g : κ -> Z} (hf :
 DenseRange f) (hg : DenseRange g) : DenseRange (Prod.map f g)
参数：hf : DenseRange f；hg : DenseRange g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_range_range_eq`：prod_range_range_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2)
· 使用定理 `Dense.prod`：Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dens
e t) : Dense (s ×ˢ t)

--- 原说明 ---
If `f` and `g` are maps with dense range, then `Prod.map f g` has dense range.
-/
theorem DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι → Y} {g : κ → Z} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using! hf.prod hg
/-
**Topology.IsInducing.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.prodMap {f : X -> Y} {g : Z -> W} (hf : IsInducing f) 
(hg : IsInducing g) : IsInducing (Prod.map f g)
参数：hf : IsInducing f；hg : IsInducing g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_comap_comap_eq`：prod_comap_comap_eq.{u, v, w, x} {α₁ : Type 
u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {
m₁ : β₁ -> α₁} {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Topology.IsInducing.prodMap {f : X → Y} {g : Z → W} (hf : IsInducing f) (hg : IsInducing g) :
    IsInducing (Prod.map f g) :=
  isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[simp]
/-
**Topology.isInducing_const_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isInducing_const_prod {x : X} {f : Y -> Z} : IsInducing (fun x' =
> (x, f x')) ↔ IsInducing f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `induced_const`：induced_const [t : TopologicalSpace α] {x : α} : (t.induc
ed fun _ : β => x) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.isInducing_const_prod {x : X} {f : Y → Z} :
    IsInducing (fun x' => (x, f x')) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[simp]
/-
**Topology.isInducing_prod_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isInducing_prod_const {y : Y} {f : X -> Z} : IsInducing (fun x =>
 (f x, y)) ↔ IsInducing f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `induced_const`：induced_const [t : TopologicalSpace α] {x : α} : (t.induc
ed fun _ : β => x) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.isInducing_prod_const {y : Y} {f : X → Z} :
    IsInducing (fun x => (f x, y)) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]
/-
**isInducing_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isInducing_prodMkLeft (y : Y) : IsInducing (fun x : X => (x, y))
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
-/
lemma isInducing_prodMkLeft (y : Y) : IsInducing (fun x : X ↦ (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id
/-
**isInducing_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isInducing_prodMkRight (x : X) : IsInducing (Prod.mk x : Y -> X × Y)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
-/
lemma isInducing_prodMkRight (x : X) : IsInducing (Prod.mk x : Y → X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id
/-
**Topology.IsEmbedding.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.prodMap {f : X -> Y} {g : Z -> W} (hf : IsEmbedding f
) (hg : IsEmbedding g) : IsEmbedding (Prod.map f g) where toIsInducing
参数：hf : IsEmbedding f；hg : IsEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.prodMap`：Topology.IsInducing.prodMap {f : X -> Y} {g
 : Z -> W} (hf : IsInducing f) (hg : IsInducing g) : IsInducing (Prod.map f g)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
lemma Topology.IsEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Prod.map f g) where
  toIsInducing := hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective
/-
**IsOpenMap.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] [inst_
3 : TopologicalSpace W] {f : X → Y} {g : Z → W},   IsOpenMap f → IsOpenMap g → I
sOpenMap (Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpenMap_iff_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X),
 nhds (f x)…
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
-/
protected theorem IsOpenMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Prod.map f g) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

@[simp]
/-
**isOpenMap_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X -> Y} {g : Z -> W} 
: IsOpenMap (Prod.map f g) ↔ IsOpenMap f ∧ IsOpenMap g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpenQuotientMap.isOpenMap_iff`：isOpenMap_iff (hf : IsOpenQuotientMap f
) {g : Y -> Z} : IsOpenMap g ↔ IsOpenMap (g ∘ f)
· 使用定理 `isOpenQuotientMap_fst`：isOpenQuotientMap_fst [Nonempty Y] : IsOpenQuotie
ntMap (Prod.fst : X × Y -> X)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `isOpenMap_fst`：isOpenMap_fst : IsOpenMap (@Prod.fst X Y)
· 使用定理 `isOpenQuotientMap_snd`：isOpenQuotientMap_snd [Nonempty X] : IsOpenQuotie
ntMap (Prod.snd : X × Y -> Y)
· 使用定理 `isOpenMap_snd`：isOpenMap_snd : IsOpenMap (@Prod.snd X Y)
· 使用定理 `IsOpenMap.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topol
ogicalS…
-/
theorem isOpenMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X → Y} {g : Z → W} :
    IsOpenMap (Prod.map f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hf, hg⟩ ↦ hf.prodMap hg⟩
  · rw [(isOpenQuotientMap_fst (Y := Z)).isOpenMap_iff]
    exact isOpenMap_fst.comp h
  · rw [(isOpenQuotientMap_snd (X := X)).isOpenMap_iff]
    exact isOpenMap_snd.comp h
/-
**Topology.IsOpenEmbedding.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmb
edding`。
形式化陈述：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] [inst_
3 : TopologicalSpace W] {f : X → Y} {g : Z → W},   Topology.IsOpenEmbedding f → 
Topology.IsOpenEmbedding g → Topology.IsOpenEmbedding (Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap`：∀ {X : Type u_1} {Y :
 Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
,   Topology.IsEmbedding f → IsOpenMap …
· 使用引理 `Topology.IsEmbedding.prodMap`：Topology.IsEmbedding.prodMap {f : X -> Y} 
{g : Z -> W} (hf : IsEmbedding f) (hg : IsEmbedding g) : IsEmbedding (Prod.map f
 g) where toIsIndu…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `IsOpenMap.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topol
ogicalS…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
protected lemma Topology.IsOpenEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) : IsOpenEmbedding (Prod.map f g) :=
  .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)
/-
**Topology.IsClosedEmbedding.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClose
dEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] [inst_
3 : TopologicalSpace W] {f : X → Y} {g : Z → W},   Topology.IsClosedEmbedding f 
→ Topology.IsClosedEmbedding g → Topology.IsClosedEmbedding (Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.prodMap`：Topology.IsEmbedding.prodMap {f : X -> Y} 
{g : Z -> W} (hf : IsEmbedding f) (hg : IsEmbedding g) : IsEmbedding (Prod.map f
 g) where toIsIndu…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
-/
protected lemma Topology.IsClosedEmbedding.prodMap {f : X → Y} {g : Z → W}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClosedEmbedding (Prod.map f g) :=
  { hf.isEmbedding.prodMap hg.isEmbedding with
    isClosed_range := range_prodMap ▸ hf.isClosed_range.prod hg.isClosed_range }
/-
**isEmbedding_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_graph {f : X -> Y} (hf : Continuous f) : IsEmbedding fun x => 
(x, f x)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
lemma isEmbedding_graph {f : X → Y} (hf : Continuous f) : IsEmbedding fun x => (x, f x) :=
  .of_comp (continuous_id.prodMk hf) continuous_fst .id
/-
**isEmbedding_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_prodMkLeft (y : Y) : IsEmbedding (fun x : X => (x, y))
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
lemma isEmbedding_prodMkLeft (y : Y) : IsEmbedding (fun x : X ↦ (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id
/-
**isEmbedding_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_prodMkRight (x : X) : IsEmbedding (Prod.mk x : Y -> X × Y)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
lemma isEmbedding_prodMkRight (x : X) : IsEmbedding (Prod.mk x : Y → X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id
/-
**IsOpenQuotientMap.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z -> W} (hf : IsOpenQuotientMa
p f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (Prod.map f g)
参数：hf : IsOpenQuotientMap f；hg : IsOpenQuotientMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Surjective f → Function.S
urjective g → Fun…
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type u_1} {Z : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topol
ogicalS…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem IsOpenQuotientMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenQuotientMap f)
    (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (Prod.map f g) :=
  ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

@[simp]
/-
**isOpenQuotientMap_prodMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenQuotientMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X -> Y} {g : 
Z -> W} : IsOpenQuotientMap (Prod.map f g) ↔ IsOpenQuotientMap f ∧ IsOpenQuotien
tMap g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem isOpenQuotientMap_prodMap_iff [Nonempty X] [Nonempty Z] {f : X → Y} {g : Z → W} :
    IsOpenQuotientMap (Prod.map f g) ↔ IsOpenQuotientMap f ∧ IsOpenQuotientMap g := by
  have : Nonempty Y := .map f inferInstance
  have : Nonempty W := .map g inferInstance
  grind [isOpenQuotientMap_iff, continuous_prodMap_iff, isOpenMap_prodMap_iff, Prod.map_surjective]
/-
**TopologicalSpace.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α} {τ₁ 
τ₂ : TopologicalSpace β} (hσ : σ₁ <= σ₂) (hτ : τ₁ <= τ₂) : @instTopologicalSpace
Prod α β σ₁ τ₁ <= @instTopologicalSpaceProd α β σ₂ τ₂
参数：hσ : σ₁ <= σ₂；hτ : τ₁ <= τ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `induced_mono`：induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans <| induced_mono hσ) (inf_le_right.trans <| induced_mono hτ)

-- Homeomorphisms between the various product: products of two homeomorphisms,
-- as well as commutativity and associativity. See below for the analogous results for sums,
-- as well as distributivity, etc.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

set_option backward.defeqAttrib.useBackward true in
/-- Product of two homeomorphisms. -/
/-
**Homeomorph.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where toEquiv
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two homeomorphisms.
-/
def prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
/-
**Homeomorph.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : (h₁.prodCongr h₂).symm = h₁
.symm.prodCongr h₂.symm
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
/-
**Homeomorph.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.ma
p h₁ h₂
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

variable (W X Y Z)

/-- `X × Y` is homeomorphic to `Y × X`. -/
/-
**Homeomorph.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodComm : X × Y ≃ₜ Y × X where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X × Y` is homeomorphic to `Y × X`.
-/
def prodComm : X × Y ≃ₜ Y × X where
  toEquiv := Equiv.prodComm X Y

@[simp]
/-
**Homeomorph.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：prodComm_symm : (prodComm X Y).symm = prodComm Y X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  rfl

@[simp]
/-
**Homeomorph.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_prodComm : ⇑(prodComm X Y) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm X Y) = Prod.swap :=
  rfl

/-- `(X × Y) × Z` is homeomorphic to `X × (Y × Z)`. -/
/-
**Homeomorph.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(X × Y) × Z` is homeomorphic to `X × (Y × Z)`.
-/
def prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where
  toEquiv := Equiv.prodAssoc X Y Z

@[simp]
/-
**Homeomorph.prodAssoc_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：prodAssoc_toEquiv : (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodAssoc_toEquiv : (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z := rfl

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
/-
**Homeomorph.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodProdProdComm : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`.
-/
def prodProdProdComm : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  toEquiv := Equiv.prodProdProdComm X Y W Z

@[simp]
/-
**Homeomorph.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：prodProdProdComm_symm : (prodProdProdComm X Y W Z).symm = prodProdProdComm
 X W Y Z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_symm : (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z :=
  rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
/-
**Homeomorph.prodPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodPUnit : X × PUnit ≃ₜ X where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X × {*}` is homeomorphic to `X`.
-/
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X

/-- `{*} × X` is homeomorphic to `X`. -/
/-
**Homeomorph.punitProd** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：punitProd : PUnit × X ≃ₜ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{*} × X` is homeomorphic to `X`.
-/
def punitProd : PUnit × X ≃ₜ X :=
  (prodComm _ _).trans (prodPUnit _)
/-
**Homeomorph.coe_punitProd** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ (X : Type u) [inst : TopologicalSpace X], ⇑(Homeomorph.punitProd X) = Pr
od.snd
参数：X : Type u；Homeomorph.punitProd X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_punitProd : ⇑(punitProd X) = Prod.snd := rfl

end Homeomorph

end Prod

section Sum

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]

/-
**continuous_sum_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sum_dom {f : X oplus Y -> Z} : Continuous f ↔ Continuous (f ∘ S
um.inl) ∧ Continuous (f ∘ Sum.inr)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_sup_dom`：continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ 
: TopologicalSpace β} : Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Conti
nuous[t₂…
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
-/
theorem continuous_sum_dom {f : X ⊕ Y → Z} :
    Continuous f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr) :=
  (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom
/-
**continuous_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sumElim {f : X -> Z} {g : Y -> Z} : Continuous (Sum.elim f g) ↔
 Continuous f ∧ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_sum_dom`：continuous_sum_dom {f : X oplus Y -> Z} : Continuous
 f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr)
-/
theorem continuous_sumElim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom

@[continuity, fun_prop]
/-
**Continuous.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : Continuous f) (hg : Con
tinuous g) : Continuous (Sum.elim f g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sumElim`：continuous_sumElim {f : X -> Z} {g : Y -> Z} : Conti
nuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g
-/
theorem Continuous.sumElim {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sumElim.2 ⟨hf, hg⟩

@[continuity, fun_prop]
/-
**continuous_isLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_isLeft : Continuous (isLeft : X oplus Y -> Bool)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sum_dom`：continuous_sum_dom {f : X oplus Y -> Z} : Continuous
 f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_isLeft : Continuous (isLeft : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
/-
**continuous_isRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_isRight : Continuous (isRight : X oplus Y -> Bool)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sum_dom`：continuous_sum_dom {f : X oplus Y -> Z} : Continuous
 f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_isRight : Continuous (isRight : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
/-
**continuous_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inl : Continuous (@inl X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩

@[continuity, fun_prop]
/-
**continuous_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inr : Continuous (@inr X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩

@[fun_prop, continuity]
/-
**continuous_sum_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_sum_swap : Continuous (@Sum.swap X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
-/
lemma continuous_sum_swap : Continuous (@Sum.swap X Y) :=
  Continuous.sumElim continuous_inr continuous_inl
/-
**isOpen_sum_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_sum_iff {s : Set (X oplus Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsO
pen (inr ⁻¹' s)
参数：X oplus Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_sum_iff {s : Set (X ⊕ Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl
/-
**isClosed_sum_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_sum_iff {s : Set (X oplus Y)} : IsClosed s ↔ IsClosed (inl ⁻¹' s)
 ∧ IsClosed (inr ⁻¹' s)
参数：X oplus Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_sum_iff {s : Set (X ⊕ Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]
/-
**isOpenMap_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_inl : IsOpenMap (@inl X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Set.preimage_inr_image_inl`：preimage_inr_image_inl (s : Set α) : Sum.inr
 ⁻¹' @Sum.inl α β '' s = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]
/-
**isOpenMap_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_inr : IsOpenMap (@inr X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_inl_image_inr`：preimage_inl_image_inr (s : Set β) : Sum.inl
 ⁻¹' @Sum.inr α β '' s = ∅
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]
/-
**isClosedMap_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_inl : IsClosedMap (@inl X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Set.preimage_inr_image_inl`：preimage_inr_image_inl (s : Set α) : Sum.inr
 ⁻¹' @Sum.inl α β '' s = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem isClosedMap_inl : IsClosedMap (@inl X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]
/-
**isClosedMap_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_inr : IsClosedMap (@inr X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_inl_image_inr`：preimage_inl_image_inr (s : Set β) : Sum.inl
 ⁻¹' @Sum.inr α β '' s = ∅
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem isClosedMap_inr : IsClosedMap (@inr X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]
/-
**Topology.IsOpenEmbedding.inl** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmbeddi
ng`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y], Topology.IsOpenEmbedding Sum.inl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `isOpenMap_inl`：isOpenMap_inl : IsOpenMap (@inl X Y)
-/
protected lemma Topology.IsOpenEmbedding.inl : IsOpenEmbedding (@inl X Y) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl
/-
**Topology.IsOpenEmbedding.inr** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmbeddi
ng`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y], Topology.IsOpenEmbedding Sum.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `isOpenMap_inr`：isOpenMap_inr : IsOpenMap (@inr X Y)
-/
protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
  .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr
/-
**Topology.IsEmbedding.inl** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y], Topology.IsEmbedding Sum.inl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
-/
protected lemma Topology.IsEmbedding.inl : IsEmbedding (@inl X Y) := IsOpenEmbedding.inl.1
/-
**Topology.IsEmbedding.inr** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y], Topology.IsEmbedding Sum.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
-/
protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1
/-
**isOpen_range_inl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpen_range_inl : IsOpen (range (inl : X -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
-/
lemma isOpen_range_inl : IsOpen (range (inl : X → X ⊕ Y)) := IsOpenEmbedding.inl.2
/-
**isOpen_range_inr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpen_range_inr : IsOpen (range (inr : Y -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
-/
lemma isOpen_range_inr : IsOpen (range (inr : Y → X ⊕ Y)) := IsOpenEmbedding.inr.2
/-
**isClosed_range_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_range_inl : IsClosed (range (inl : X -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.compl_range_inl`：compl_range_inl : (range (Sum.inl : α -> α oplus β)
)ᶜ = range (Sum.inr : β -> α oplus β)
· 使用引理 `isOpen_range_inr`：isOpen_range_inr : IsOpen (range (inr : Y -> X oplus Y
))
-/
theorem isClosed_range_inl : IsClosed (range (inl : X → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr
/-
**isClosed_range_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_range_inr : IsClosed (range (inr : Y -> X oplus Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.compl_range_inr`：compl_range_inr : (range (Sum.inr : β -> α oplus β)
)ᶜ = range (Sum.inl : α -> α oplus β)
· 使用引理 `isOpen_range_inl`：isOpen_range_inl : IsOpen (range (inl : X -> X oplus Y
))
-/
theorem isClosed_range_inr : IsClosed (range (inr : Y → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl
/-
**Topology.IsClosedEmbedding.inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X -> X oplus Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl
· 使用定理 `isClosed_range_inl`：isClosed_range_inl : IsClosed (range (inl : X -> X o
plus Y))
-/
theorem Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X → X ⊕ Y) :=
  ⟨.inl, isClosed_range_inl⟩
/-
**Topology.IsClosedEmbedding.inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y -> X oplus Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inr
· 使用定理 `isClosed_range_inr`：isClosed_range_inr : IsClosed (range (inr : Y -> X o
plus Y))
-/
theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y → X ⊕ Y) :=
  ⟨.inr, isClosed_range_inr⟩
/-
**nhds_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inl (x : X) : 𝓝 (inl x : X oplus Y) = map inl (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
-/
theorem nhds_inl (x : X) : 𝓝 (inl x : X ⊕ Y) = map inl (𝓝 x) :=
  (IsOpenEmbedding.inl.map_nhds_eq _).symm
/-
**nhds_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inr (y : Y) : 𝓝 (inr y : X oplus Y) = map inr (𝓝 y)
参数：y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
-/
theorem nhds_inr (y : Y) : 𝓝 (inr y : X ⊕ Y) = map inr (𝓝 y) :=
  (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]
/-
**continuous_sumMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sumMap {f : X -> Y} {g : Z -> W} : Continuous (Sum.map f g) ↔ C
ontinuous f ∧ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_sumElim`：continuous_sumElim {f : X -> Z} {g : Y -> Z} : Conti
nuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl
· 使用定理 `Topology.IsEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inr
-/
theorem continuous_sumMap {f : X → Y} {g : Z → W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sumElim.trans <|
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[continuity, fun_prop]
/-
**Continuous.sumMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sumMap {f : X -> Y} {g : Z -> W} (hf : Continuous f) (hg : Cont
inuous g) : Continuous (Sum.map f g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sumMap`：continuous_sumMap {f : X -> Y} {g : Z -> W} : Continu
ous (Sum.map f g) ↔ Continuous f ∧ Continuous g
-/
theorem Continuous.sumMap {f : X → Y} {g : Z → W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sumMap.2 ⟨hf, hg⟩
/-
**isOpenMap_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_sum {f : X oplus Y -> Z} : IsOpenMap f ↔ (IsOpenMap fun a => f (
inl a)) ∧ IsOpenMap fun b => f (inr b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nhds_inl`：nhds_inl (x : X) : 𝓝 (inl x : X oplus Y) = map inl (𝓝 x)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `nhds_inr`：nhds_inr (y : Y) : 𝓝 (inr y : X oplus Y) = map inr (𝓝 y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpenMap_sum {f : X ⊕ Y → Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]
/-
**IsOpenMap.sumMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.sumMap {f : X -> Y} {g : Z -> W} (hf : IsOpenMap f) (hg : IsOpen
Map g) : IsOpenMap (Sum.map f g)
参数：hf : IsOpenMap f；hg : IsOpenMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_sum`：isOpenMap_sum {f : X oplus Y -> Z} : IsOpenMap f ↔ (IsOpe
nMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `isOpenMap_inl`：isOpenMap_inl : IsOpenMap (@inl X Y)
· 使用定理 `isOpenMap_inr`：isOpenMap_inr : IsOpenMap (@inr X Y)
-/
theorem IsOpenMap.sumMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.map f g) :=
  isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]
/-
**isOpenMap_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_sumElim {f : X -> Z} {g : Y -> Z} : IsOpenMap (Sum.elim f g) ↔ I
sOpenMap f ∧ IsOpenMap g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpenMap_sumElim {f : X → Z} {g : Y → Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]
/-
**IsOpenMap.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsOpenMap f) (hg : IsOpe
nMap g) : IsOpenMap (Sum.elim f g)
参数：hf : IsOpenMap f；hg : IsOpenMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_sumElim`：isOpenMap_sumElim {f : X -> Z} {g : Y -> Z} : IsOpenM
ap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g
-/
theorem IsOpenMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sumElim.2 ⟨hf, hg⟩
/-
**Topology.IsOpenEmbedding.sumElim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsOpenEmb
edding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) : IsOpenEmbedd
ing (Sum.elim f g)
参数：hf : IsOpenEmbedding f；hg : IsOpenEmbedding g；h : Injective (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap`：∀ {X : Type
 u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologic
alSpace Y],   Topology.IsOpenEmbedding f ↔ Contin…
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpenMap.sumElim`：IsOpenMap.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsO
penMap f) (hg : IsOpenMap g) : IsOpenMap (Sum.elim f g)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Topology.IsOpenEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) :
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩
/-
**isClosedMap_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_sum {f : X oplus Y -> Z} : IsClosedMap f ↔ (IsClosedMap fun a 
=> f (.inl a)) ∧ IsClosedMap fun b => f (.inr b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Topology.IsClosedEmbedding.inl`：Topology.IsClosedEmbedding.inl : IsClose
dEmbedding (inl : X -> X oplus Y)
· 使用定理 `Topology.IsClosedEmbedding.inr`：Topology.IsClosedEmbedding.inr : IsClose
dEmbedding (inr : Y -> X oplus Y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_sum_iff`：isClosed_sum_iff {s : Set (X oplus Y)} : IsClosed s ↔ 
IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isClosedMap_sum {f : X ⊕ Y → Z} :
    IsClosedMap f ↔ (IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b) := by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert! (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]
/-
**IsClosedMap.sumMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.sumMap {f : X -> Y} {g : Z -> W} (hf : IsClosedMap f) (hg : Is
ClosedMap g) : IsClosedMap (Sum.map f g)
参数：hf : IsClosedMap f；hg : IsClosedMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosedMap_sum`：isClosedMap_sum {f : X oplus Y -> Z} : IsClosedMap f ↔ 
(IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b)
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `isClosedMap_inl`：isClosedMap_inl : IsClosedMap (@inl X Y)
· 使用定理 `isClosedMap_inr`：isClosedMap_inr : IsClosedMap (@inr X Y)
-/
theorem IsClosedMap.sumMap {f : X → Y} {g : Z → W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.map f g) :=
  isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]
/-
**isClosedMap_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_sumElim {f : X -> Z} {g : Y -> Z} : IsClosedMap (Sum.elim f g)
 ↔ IsClosedMap f ∧ IsClosedMap g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosedMap_sumElim {f : X → Z} {g : Y → Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]
/-
**IsClosedMap.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsClosedMap f) (hg : I
sClosedMap g) : IsClosedMap (Sum.elim f g)
参数：hf : IsClosedMap f；hg : IsClosedMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosedMap_sumElim`：isClosedMap_sumElim {f : X -> Z} {g : Y -> Z} : IsC
losedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g
-/
theorem IsClosedMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sumElim.2 ⟨hf, hg⟩
/-
**Topology.IsClosedEmbedding.sumElim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.sumElim {f : X -> Z} {g : Y -> Z} (hf : IsClose
dEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) : IsClos
edEmbedding (Sum.elim f g)
参数：hf : IsClosedEmbedding f；hg : IsClosedEmbedding g；h : Injective (Sum.elim f g
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_is
ClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 :
 TopologicalSpace Y] {f : X → Y},   Topology.IsClosedEmbedding f ↔ Cont…
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsClosedMap.sumElim`：IsClosedMap.sumElim {f : X -> Z} {g : Y -> Z} (hf :
 IsClosedMap f) (hg : IsClosedMap g) : IsClosedMap (Sum.elim f g)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Topology.IsClosedEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

-- Homeomorphisms between the various constructions: sums of two homeomorphisms,
-- as well as commutativity, associativity and distributivity with products.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

set_option backward.defeqAttrib.useBackward true in
/-- Sum of two homeomorphisms. -/
/-
**Homeomorph.sumCongr** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X oplus Y ≃ₜ X' oplus Y' where to
Equiv
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum of two homeomorphisms.
-/
def sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X ⊕ Y ≃ₜ X' ⊕ Y' where
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]
/-
**Homeomorph.sumCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：sumCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : (sumCongr h₁ h₂).symm = sumC
ongr h₁.symm h₂.symm
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (sumCongr h₁ h₂).symm = sumCongr h₁.symm h₂.symm := rfl

@[simp]
/-
**Homeomorph.sumCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：sumCongr_refl : sumCongr (.refl X) (.refl Y) = .refl (X oplus Y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sumCongr_refl : sumCongr (.refl X) (.refl Y) = .refl (X ⊕ Y) := by
  ext i
  cases i <;> rfl

@[simp]
/-
**Homeomorph.sumCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：sumCongr_trans {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace 
Y''] (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') (h₃ : X' ≃ₜ X'') (h₄ : Y' ≃ₜ Y'') : (sumCongr
 h₁ h₂).trans (sumCongr h₃ h₄) = sumCongr (h₁.trans h₃) (h₂.trans h₄)
参数：h₁ : X ≃ₜ X'；h₂ : Y ≃ₜ Y'；h₃ : X' ≃ₜ X''；h₄ : Y' ≃ₜ Y''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sumCongr_trans {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
    (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') (h₃ : X' ≃ₜ X'') (h₄ : Y' ≃ₜ Y'') :
    (sumCongr h₁ h₂).trans (sumCongr h₃ h₄) = sumCongr (h₁.trans h₃) (h₂.trans h₄) := by
  ext i
  cases i <;> rfl

variable (W X Y Z)

/-- `X ⊕ Y` is homeomorphic to `Y ⊕ X`. -/
/-
**Homeomorph.sumComm** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumComm : X oplus Y ≃ₜ Y oplus X where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X ⊕ Y` is homeomorphic to `Y ⊕ X`.
-/
def sumComm : X ⊕ Y ≃ₜ Y ⊕ X where
  toEquiv := Equiv.sumComm X Y

@[simp]
/-
**Homeomorph.sumComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：sumComm_symm : (sumComm X Y).symm = sumComm Y X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumComm_symm : (sumComm X Y).symm = sumComm Y X :=
  rfl

@[simp]
/-
**Homeomorph.coe_sumComm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_sumComm : ⇑(sumComm X Y) = Sum.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumComm : ⇑(sumComm X Y) = Sum.swap :=
  rfl

@[continuity, fun_prop]
/-
**Homeomorph.continuous_sumAssoc** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：continuous_sumAssoc : Continuous (Equiv.sumAssoc X Y Z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
-/
lemma continuous_sumAssoc : Continuous (Equiv.sumAssoc X Y Z) :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]
/-
**Homeomorph.continuous_sumAssoc_symm** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：continuous_sumAssoc_symm : Continuous (Equiv.sumAssoc X Y Z).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
-/
lemma continuous_sumAssoc_symm : Continuous (Equiv.sumAssoc X Y Z).symm :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

/-- `(X ⊕ Y) ⊕ Z` is homeomorphic to `X ⊕ (Y ⊕ Z)`. -/
/-
**Homeomorph.sumAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumAssoc : (X oplus Y) oplus Z ≃ₜ X oplus Y oplus Z where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(X ⊕ Y) ⊕ Z` is homeomorphic to `X ⊕ (Y ⊕ Z)`.
-/
def sumAssoc : (X ⊕ Y) ⊕ Z ≃ₜ X ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumAssoc X Y Z

@[simp]
/-
**Homeomorph.sumAssoc_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：sumAssoc_toEquiv : (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumAssoc_toEquiv : (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z := rfl

set_option backward.defeqAttrib.useBackward true in
/-- Four-way commutativity of the disjoint union. The name matches `add_add_add_comm`. -/
/-
**Homeomorph.sumSumSumComm** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumSumSumComm : (X oplus Y) oplus W oplus Z ≃ₜ (X oplus W) oplus Y oplus Z
 where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four-way commutativity of the disjoint union. The name matches `add_add_add_comm
`.
-/
def sumSumSumComm : (X ⊕ Y) ⊕ W ⊕ Z ≃ₜ (X ⊕ W) ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumSumSumComm X Y W Z

@[simp]
/-
**Homeomorph.sumSumSumComm_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：sumSumSumComm_toEquiv : (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSum
Comm W X Y Z)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumSumSumComm_toEquiv : (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSumComm W X Y Z) := rfl

@[simp]
/-
**Homeomorph.sumSumSumComm_symm** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：sumSumSumComm_symm : (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumSumSumComm_symm : (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z) := rfl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
/-
**Homeomorph.sumEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumEmpty [IsEmpty Y] : X oplus Y ≃ₜ X where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of `X` with any empty topological space is homeomorphic to `X`.
-/
def sumEmpty [IsEmpty Y] : X ⊕ Y ≃ₜ X where
  toEquiv := Equiv.sumEmpty X Y

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
/-
**Homeomorph.emptySum** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：emptySum [IsEmpty Y] : Y oplus X ≃ₜ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of `X` with any empty topological space is homeomorphic to `X`.
-/
def emptySum [IsEmpty Y] : Y ⊕ X ≃ₜ X := (sumComm Y X).trans (sumEmpty X Y)
/-
**Homeomorph.coe_emptySum** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ (X : Type u) (Y : Type v) [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] [inst_2 : IsEmpty Y],   (Homeomorph.emptySum X Y).toEquiv = Equiv.em
ptySum Y X
参数：X : Type u；Y : Type v；Homeomorph.emptySum X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_emptySum [IsEmpty Y] : (emptySum X Y).toEquiv = Equiv.emptySum Y X := rfl

variable {W X Y Z}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`. -/
@[simps!]
/-
**Homeomorph.sumProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：sumProdDistrib : (X oplus Y) × Z ≃ₜ (X × Z) oplus (Y × Z)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`.
-/
def sumProdDistrib : (X ⊕ Y) × Z ≃ₜ (X × Z) ⊕ (Y × Z) :=
  Homeomorph.symm <|
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

/-- `X × (Y ⊕ Z)` is homeomorphic to `X × Y ⊕ X × Z`. -/
/-
**Homeomorph.prodSumDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：prodSumDistrib : X × (Y oplus Z) ≃ₜ (X × Y) oplus (X × Z)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X × (Y ⊕ Z)` is homeomorphic to `X × Y ⊕ X × Z`.
-/
def prodSumDistrib : X × (Y ⊕ Z) ≃ₜ (X × Y) ⊕ (X × Z) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)

end Homeomorph

section IsInducing

variable {f : X → Z} {g : Y → Z}

/-- If `Sum.elim f g` is an inducing map, then so is `f`. -/
/-
**Topology.IsInducing.sumElim_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.sumElim_left (h : IsInducing (Sum.elim f g)) : IsInduc
ing f
参数：h : IsInducing (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl
· 使用定理 `Sum.elim_comp_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inl = f

--- 原说明 ---
If `Sum.elim f g` is an inducing map, then so is `f`.
-/
lemma Topology.IsInducing.sumElim_left (h : IsInducing (Sum.elim f g)) : IsInducing f :=
  elim_comp_inl f g ▸ h.comp IsEmbedding.inl.isInducing

/-- If `Sum.elim f g` is an inducing map, then so is `g`. -/
/-
**Topology.IsInducing.sumElim_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.sumElim_right (h : IsInducing (Sum.elim f g)) : IsIndu
cing g
参数：h : IsInducing (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inr
· 使用定理 `Sum.elim_comp_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inr = g

--- 原说明 ---
If `Sum.elim f g` is an inducing map, then so is `g`.
-/
lemma Topology.IsInducing.sumElim_right (h : IsInducing (Sum.elim f g)) : IsInducing g :=
  elim_comp_inr f g ▸ h.comp IsEmbedding.inr.isInducing

/-- If `f` and `g` are inducing maps whose ranges are separated, then `Sum.elim f g` is inducing. -/
/-
**Topology.IsInducing.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.sumElim (hf : IsInducing f) (hg : IsInducing g) (hFg :
 Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (ran
ge g))) : IsInducing (Sum.elim f g)
参数：hf : IsInducing f；hg : IsInducing g；hFg : Disjoint (closure (range f)) (range
 g)；hfG : Disjoint (range f) (closure (range g))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_sumElim_eq`：comap_sumElim_eq (l : Filter γ) (m₁ : α -> γ) (
m₂ : β -> γ) : comap (Sum.elim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap 
m₂ l)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `nhds_inl`：nhds_inl (x : X) : 𝓝 (inl x : X oplus Y) = map inl (𝓝 x)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Filter.map_eq_bot_iff`：map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥
· 使用定理 `Filter.comap_eq_bot_iff_compl_range`：comap_eq_bot_iff_compl_range {f : F
ilter β} {m : α -> β} : comap m f = ⊥ ↔ (range m)ᶜ in f
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `disjoint_nhdsSet_principal`：disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s)
 (𝓟 t) ↔ Disjoint s (closure t)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `nhds_inr`：nhds_inr (y : Y) : 𝓝 (inr y : X oplus Y) = map inr (𝓝 y)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Filter.disjoint_principal_left`：disjoint_principal_left {f : Filter α} {
s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ in f
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `disjoint_principal_nhdsSet`：disjoint_principal_nhdsSet : Disjoint (𝓟 s) 
(𝓝ˢ t) ↔ Disjoint (closure s) t

--- 原说明 ---
If `f` and `g` are inducing maps whose ranges are separated, then `Sum.elim f g`
 is inducing.
-/
theorem Topology.IsInducing.sumElim (hf : IsInducing f) (hg : IsInducing g)
    (hFg : Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (range g))) :
    IsInducing (Sum.elim f g) := by
  rw [← disjoint_principal_nhdsSet] at hFg
  rw [← disjoint_nhdsSet_principal] at hfG
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm ((hf.continuous.sumElim hg.continuous).tendsto x).le_comap
  obtain x | x := x <;>
  simp only [comap_sumElim_eq, nhds_inl, nhds_inr, elim_inl, elim_inr, ← hf.nhds_eq_comap,
    ← hg.nhds_eq_comap, sup_le_iff, le_rfl, true_and, and_true] <;>
  convert! bot_le (α := Filter (X ⊕ Y)) <;>
  rw [map_eq_bot_iff, comap_eq_bot_iff_compl_range]
  · rw [← disjoint_principal_right]
    exact hfG.mono_left (nhds_le_nhdsSet (mem_range_self x))
  · rw [← disjoint_principal_left]
    exact hFg.mono_right (nhds_le_nhdsSet (mem_range_self x))

/-- If `Sum.elim f g` is inducing, `closure (range f)` and `range g` must be disjoint.
This is an auxiliary result towards proving `isInducing_sumElim`. -/
/-
**Topology.IsInducing.disjoint_of_sumElim_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.disjoint_of_sumElim_aux (h : IsInducing (Sum.elim f g)
) : Disjoint (closure (range f)) (range g)
参数：h : IsInducing (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `isClosed_range_inl`：isClosed_range_inl : IsClosed (range (inl : X -> X o
plus Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.elim_comp_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inl = f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.disjoint_image_right`：disjoint_image_right {f : α -> β} {s : Set α} 
{t : Set β} : Disjoint t (f '' s) ↔ Disjoint (f ⁻¹' t) s
· 使用定理 `Sum.elim_comp_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inr = g
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.disjoint_image_inl_image_inr`：disjoint_image_inl_image_inr {u : Set 
α} {v : Set β} : Disjoint (Sum.inl '' u) (Sum.inr '' v)
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c

--- 原说明 ---
If `Sum.elim f g` is inducing, `closure (range f)` and `range g` must be disjoin
t.
This is an auxiliary result towards proving `isInducing_sumElim`.
-/
theorem Topology.IsInducing.disjoint_of_sumElim_aux (h : IsInducing (Sum.elim f g)) :
    Disjoint (closure (range f)) (range g) := by
  rcases h.isClosed_iff.mp isClosed_range_inl with ⟨C, C_closed, hC⟩
  have A : closure (range f) ⊆ C := by
    rw [C_closed.closure_subset_iff, ← elim_comp_inl f g, range_comp, image_subset_iff, hC]
  have B : Disjoint C (range g) := by
    rw [← image_univ, disjoint_image_right, ← elim_comp_inr f g, preimage_comp, hC,
        ← disjoint_image_right, ← image_univ]
    exact disjoint_image_inl_image_inr
  exact B.mono_left A
/-
**Topology.IsOpenEmbedding.sumSwap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.sumSwap : IsOpenEmbedding (@Sum.swap X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem Topology.IsOpenEmbedding.sumSwap : IsOpenEmbedding (@Sum.swap X Y) :=
  (Homeomorph.sumComm X Y).isOpenEmbedding
/-
**Topology.IsInducing.sumSwap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.sumSwap : IsInducing (@Sum.swap X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `Topology.IsOpenEmbedding.sumSwap`：Topology.IsOpenEmbedding.sumSwap : IsO
penEmbedding (@Sum.swap X Y)
-/
theorem Topology.IsInducing.sumSwap : IsInducing (@Sum.swap X Y) :=
  IsOpenEmbedding.sumSwap.isInducing
/-
**isInducing_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isInducing_sumElim : IsInducing (Sum.elim f g) ↔ IsInducing f ∧ IsInducing
 g ∧ Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (range
 g))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.sumElim_left`：Topology.IsInducing.sumElim_left (h : 
IsInducing (Sum.elim f g)) : IsInducing f
· 使用引理 `Topology.IsInducing.sumElim_right`：Topology.IsInducing.sumElim_right (h 
: IsInducing (Sum.elim f g)) : IsInducing g
· 使用定理 `Topology.IsInducing.disjoint_of_sumElim_aux`：Topology.IsInducing.disjoin
t_of_sumElim_aux (h : IsInducing (Sum.elim f g)) : Disjoint (closure (range f)) 
(range g)
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `Topology.IsInducing.sumSwap`：Topology.IsInducing.sumSwap : IsInducing (@
Sum.swap X Y)
· 使用定理 `Sum.elim_swap`：elim_swap {α β γ : Type*} {f : α -> γ} {g : β -> γ} : Sum
.elim f g ∘ Sum.swap = Sum.elim g f
· 使用定理 `Topology.IsInducing.sumElim`：Topology.IsInducing.sumElim (hf : IsInducin
g f) (hg : IsInducing g) (hFg : Disjoint (closure (range f)) (range g)) (hfG : D
isjoint (range f)…
-/
theorem isInducing_sumElim :
    IsInducing (Sum.elim f g) ↔ IsInducing f ∧ IsInducing g ∧
      Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (range g)) :=
  ⟨fun h ↦ ⟨h.sumElim_left, h.sumElim_right, h.disjoint_of_sumElim_aux,
    ((Sum.elim_swap ▸ h.comp .sumSwap).disjoint_of_sumElim_aux ).symm⟩,
    fun ⟨hf, hg, hFg, hfG⟩ ↦ hf.sumElim hg hFg hfG⟩
/-
**Topology.IsInducing.sumElim_of_separatedNhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.sumElim_of_separatedNhds (hf : IsInducing f) (hg : IsI
nducing g) (hsep : SeparatedNhds (range f) (range g)) : IsInducing (Sum.elim f g
)
参数：hf : IsInducing f；hg : IsInducing g；hsep : SeparatedNhds (range f) (range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.sumElim`：Topology.IsInducing.sumElim (hf : IsInducin
g f) (hg : IsInducing g) (hFg : Disjoint (closure (range f)) (range g)) (hfG : D
isjoint (range f)…
· 使用定理 `SeparatedNhds.disjoint_closure_left`：disjoint_closure_left (h : Separate
dNhds s t) : Disjoint (closure s) t
· 使用定理 `SeparatedNhds.disjoint_closure_right`：disjoint_closure_right (h : Separa
tedNhds s t) : Disjoint s (closure t)
-/
lemma Topology.IsInducing.sumElim_of_separatedNhds
    (hf : IsInducing f) (hg : IsInducing g) (hsep : SeparatedNhds (range f) (range g)) :
    IsInducing (Sum.elim f g) :=
  hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

/-- If `Sum.elim f g` is an embedding, then so is `f`. -/
/-
**Topology.IsEmbedding.sumElim_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.sumElim_left (h : IsEmbedding (Sum.elim f g)) : IsEmb
edding f
参数：h : IsEmbedding (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl
· 使用定理 `Sum.elim_comp_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inl = f

--- 原说明 ---
If `Sum.elim f g` is an embedding, then so is `f`.
-/
lemma Topology.IsEmbedding.sumElim_left (h : IsEmbedding (Sum.elim f g)) : IsEmbedding f :=
  elim_comp_inl f g ▸ h.comp IsEmbedding.inl

/-- If `Sum.elim f g` is an embedding, then so is `g`. -/
/-
**Topology.IsEmbedding.sumElim_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.sumElim_right (h : IsEmbedding (Sum.elim f g)) : IsEm
bedding g
参数：h : IsEmbedding (Sum.elim f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inr
· 使用定理 `Sum.elim_comp_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inr = g

--- 原说明 ---
If `Sum.elim f g` is an embedding, then so is `g`.
-/
lemma Topology.IsEmbedding.sumElim_right (h : IsEmbedding (Sum.elim f g)) : IsEmbedding g :=
  elim_comp_inr f g ▸ h.comp IsEmbedding.inr
/-
**isEmbedding_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmbedding_sumElim : IsEmbedding (Sum.elim f g) ↔ IsEmbedding f ∧ IsEmbed
ding g ∧ Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (r
ange g))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem isEmbedding_sumElim :
    IsEmbedding (Sum.elim f g) ↔ IsEmbedding f ∧ IsEmbedding g ∧
      Disjoint (closure (range f)) (range g) ∧ Disjoint (range f) (closure (range g)) := by
  simp_rw [isEmbedding_iff, isInducing_sumElim, Sum.elim_injective]
  constructor
  · intro ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, f_ne_g⟩⟩
    exact ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
  · intro ⟨⟨hf₁, hf₂⟩, ⟨hg₁, hg₂⟩, hFg, hfG⟩
    refine ⟨⟨hf₁, hg₁, hFg, hfG⟩, ⟨hf₂, hg₂, ?_⟩⟩
    exact fun a b ↦ hfG.ne_of_mem (mem_range_self a) (subset_closure (mem_range_self b))

/-- If `f` and `g` are embeddings whose ranges are separated, `Sum.elim f g` is an embedding. -/
/-
**Topology.IsEmbedding.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.sumElim (hf : IsEmbedding f) (hg : IsEmbedding g) (hF
g : Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (
range g))) : IsEmbedding (Sum.elim f g)
参数：hf : IsEmbedding f；hg : IsEmbedding g；hFg : Disjoint (closure (range f)) (ran
ge g)；hfG : Disjoint (range f) (closure (range g))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isEmbedding_sumElim`：isEmbedding_sumElim : IsEmbedding (Sum.elim f g) ↔ 
IsEmbedding f ∧ IsEmbedding g ∧ Disjoint (closure (range f)) (range g) ∧ Disjoin
t (range …

--- 原说明 ---
If `f` and `g` are embeddings whose ranges are separated, `Sum.elim f g` is an e
mbedding.
-/
theorem Topology.IsEmbedding.sumElim (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hFg : Disjoint (closure (range f)) (range g)) (hfG : Disjoint (range f) (closure (range g))) :
    IsEmbedding (Sum.elim f g) :=
  isEmbedding_sumElim.mpr ⟨hf, hg, hFg, hfG⟩
/-
**Topology.IsEmbedding.sumElim_of_separatedNhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.sumElim_of_separatedNhds (hf : IsEmbedding f) (hg : I
sEmbedding g) (hsep : SeparatedNhds (range f) (range g)) : IsEmbedding (Sum.elim
 f g)
参数：hf : IsEmbedding f；hg : IsEmbedding g；hsep : SeparatedNhds (range f) (range g
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.sumElim`：Topology.IsEmbedding.sumElim (hf : IsEmbed
ding f) (hg : IsEmbedding g) (hFg : Disjoint (closure (range f)) (range g)) (hfG
 : Disjoint (range…
· 使用定理 `SeparatedNhds.disjoint_closure_left`：disjoint_closure_left (h : Separate
dNhds s t) : Disjoint (closure s) t
· 使用定理 `SeparatedNhds.disjoint_closure_right`：disjoint_closure_right (h : Separa
tedNhds s t) : Disjoint s (closure t)
-/
lemma Topology.IsEmbedding.sumElim_of_separatedNhds
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hsep : SeparatedNhds (range f) (range g)) :
    IsEmbedding (Sum.elim f g) :=
  hf.sumElim hg hsep.disjoint_closure_left hsep.disjoint_closure_right

end IsInducing

end Sum

