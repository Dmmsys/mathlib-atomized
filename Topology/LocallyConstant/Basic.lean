/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Sets.Closeds

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `IsLocallyConstant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `LocallyConstant X Y` : the type of locally constant maps from `X` to `Y`
* `LocallyConstant.map` : push-forward of locally constant maps
* `LocallyConstant.comap` : pull-back of locally constant maps
-/

@[expose] public section

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter
open scoped Topology

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
/-
**IsLocallyConstant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocallyConstant (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between topological spaces is locally constant if the preimage of any
 set is open.
-/
def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ s : Set Y, IsOpen (f ⁻¹' s)

namespace IsLocallyConstant

open List in
/-
**IsLocallyConstant.tfae** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] (f : X → Y),  
 [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds x, f x' = f x, ∀ (x : X), 
IsOpen {x' | f x' = f x},       ∀ (y : Y), IsOpen (f ⁻¹' {y}), ∀ (x : X), ∃ U, I
sOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x].TFAE
参数：f : X → Y；x : X；x' : X；x : X；y : Y；f ⁻¹' {y}；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
protected theorem tfae (f : X → Y) :
    TFAE [IsLocallyConstant f,
      ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x,
      ∀ x, IsOpen { x' | f x' = f x },
      ∀ y, IsOpen (f ⁻¹' {y}),
      ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x] := by
  tfae_have 1 → 4 := fun h y => h {y}
  tfae_have 4 → 3 := fun h x => h (f x)
  tfae_have 3 → 2 := fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 → 5
  | h, x => by
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 → 1
  | h, s => by
    refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
    rcases h x with ⟨U, hU, hxU, eq⟩
    exact ⟨U, fun x' hx' => mem_preimage.2 <| (eq x' hx').symm ▸ hx, hU, hxU⟩
  tfae_finish

@[nontriviality]
/-
**IsLocallyConstant.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：of_discrete [DiscreteTopology X] (f : X -> Y) : IsLocallyConstant f
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
theorem of_discrete [DiscreteTopology X] (f : X → Y) : IsLocallyConstant f := fun _ =>
  isOpen_discrete _
/-
**IsLocallyConstant.isOpen_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：isOpen_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x 
| f x = y }
参数：hf : IsLocallyConstant f；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOpen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}
/-
**IsLocallyConstant.isClosed_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`
。
形式化陈述：isClosed_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed 
{ x | f x = y }
参数：hf : IsLocallyConstant f；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isClosed_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf {y}ᶜ⟩
/-
**IsLocallyConstant.isClopen_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`
。
形式化陈述：isClopen_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen 
{ x | f x = y }
参数：hf : IsLocallyConstant f；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.isClosed_fiber`：isClosed_fiber {f : X -> Y} (hf : IsLo
callyConstant f) (y : Y) : IsClosed { x | f x = y }
· 使用定理 `IsLocallyConstant.isOpen_fiber`：isOpen_fiber {f : X -> Y} (hf : IsLocall
yConstant f) (y : Y) : IsOpen { x | f x = y }
-/
theorem isClopen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨isClosed_fiber hf _, isOpen_fiber hf _⟩
/-
**IsLocallyConstant.iff_exists_open** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant
`。
形式化陈述：iff_exists_open (f : X -> Y) : IsLocallyConstant f ↔ forall x, exists U : 
Set X, IsOpen U ∧ x in U ∧ forall x' in U, f x' = f x
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocallyConstant.tfae`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] (f : X → Y),   [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds 
x, f x' = f …
-/
theorem iff_exists_open (f : X → Y) :
    IsLocallyConstant f ↔ ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4
/-
**IsLocallyConstant.iff_eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConsta
nt`。
形式化陈述：iff_eventually_eq (f : X -> Y) : IsLocallyConstant f ↔ forall x, forallᶠ y
 in 𝓝 x, f y = f x
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocallyConstant.tfae`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] (f : X → Y),   [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds 
x, f x' = f …
-/
theorem iff_eventually_eq (f : X → Y) : IsLocallyConstant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1
/-
**IsLocallyConstant.exists_open** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：exists_open {f : X -> Y} (hf : IsLocallyConstant f) (x : X) : exists U : S
et X, IsOpen U ∧ x in U ∧ forall x' in U, f x' = f x
参数：hf : IsLocallyConstant f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocallyConstant.iff_exists_open`：iff_exists_open (f : X -> Y) : IsLoca
llyConstant f ↔ forall x, exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, 
f x' = f x
-/
theorem exists_open {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x :=
  (iff_exists_open f).1 hf x
/-
**IsLocallyConstant.eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] {f : X → Y},  
 IsLocallyConstant f → ∀ (x : X), ∀ᶠ (y : X) in nhds x, f y = f x
参数：x : X；y : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocallyConstant.iff_eventually_eq`：iff_eventually_eq (f : X -> Y) : Is
LocallyConstant f ↔ forall x, forallᶠ y in 𝓝 x, f y = f x
-/
protected theorem eventually_eq {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∀ᶠ y in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x
/-
**IsLocallyConstant.iff_isOpen_fiber_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyC
onstant`。
形式化陈述：iff_isOpen_fiber_apply {f : X -> Y} : IsLocallyConstant f ↔ forall x, IsOp
en (f ⁻¹' {f x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocallyConstant.tfae`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] (f : X → Y),   [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds 
x, f x' = f …
-/
theorem iff_isOpen_fiber_apply {f : X → Y} : IsLocallyConstant f ↔ ∀ x, IsOpen (f ⁻¹' {f x}) :=
  (IsLocallyConstant.tfae f).out 0 2
/-
**IsLocallyConstant.iff_isOpen_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstan
t`。
形式化陈述：iff_isOpen_fiber {f : X -> Y} : IsLocallyConstant f ↔ forall y, IsOpen (f 
⁻¹' {y})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocallyConstant.tfae`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] (f : X → Y),   [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds 
x, f x' = f …
-/
theorem iff_isOpen_fiber {f : X → Y} : IsLocallyConstant f ↔ ∀ y, IsOpen (f ⁻¹' {y}) :=
  (IsLocallyConstant.tfae f).out 0 3
/-
**IsLocallyConstant.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsLocallyConstant f → Continuous f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem continuous [TopologicalSpace Y] {f : X → Y} (hf : IsLocallyConstant f) :
    Continuous f :=
  ⟨fun _ _ => hf _⟩
/-
**IsLocallyConstant.iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`
。
形式化陈述：iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X -> Y) 
: IsLocallyConstant f ↔ Continuous f
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocallyConstant
 f → Continuous f
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X → Y) :
    IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩
/-
**IsLocallyConstant.of_constant** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：of_constant (f : X -> Y) (h : forall x y, f x = f y) : IsLocallyConstant f
参数：f : X -> Y；h : forall x y, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_eventually_eq`：iff_eventually_eq (f : X -> Y) : Is
LocallyConstant f ↔ forall x, forallᶠ y in 𝓝 x, f y = f x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem of_constant (f : X → Y) (h : ∀ x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2 fun _ => Eventually.of_forall fun _ => h _ _
/-
**IsLocallyConstant.const** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] (y : Y), IsLoc
allyConstant (Function.const X y)
参数：y : Y；Function.const X y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.of_constant`：of_constant (f : X -> Y) (h : forall x y,
 f x = f y) : IsLocallyConstant f
-/
protected theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  of_constant _ fun _ _ => rfl
/-
**IsLocallyConstant.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 {f : X → Y},   IsLocallyConstant f → ∀ (g : Y → Z), IsLocallyConstant (g ∘ f)
参数：g : Y → Z；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
protected theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) :
    IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf _
/-
**IsLocallyConstant.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：prodMk {Y'} {f : X -> Y} {f' : X -> Y'} (hf : IsLocallyConstant f) (hf' : 
IsLocallyConstant f') : IsLocallyConstant fun x => (f x, f' x)
参数：hf : IsLocallyConstant f；hf' : IsLocallyConstant f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_eventually_eq`：iff_eventually_eq (f : X -> Y) : Is
LocallyConstant f ↔ forall x, forallᶠ y in 𝓝 x, f y = f x
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsLocallyConstant.eventually_eq`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] {f : X → Y},   IsLocallyConstant f → ∀ (x : X), ∀ᶠ (y : X) 
in nhds x, f y = f x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem prodMk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f)
    (hf' : IsLocallyConstant f') : IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2 fun x =>
    (hf.eventually_eq x).mp <| (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'
/-
**IsLocallyConstant.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 {f : X → Y},   IsLocallyConstant f → ∀ (g : Y → Z), IsLocallyConstant (g ∘ f)
参数：g : Y → Z；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (h : Y₁ → Y₂ → Z) : IsLocallyConstant fun x => h (f x) (g x) :=
  (hf.prodMk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2
/-
**IsLocallyConstant.comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant
`。
形式化陈述：comp_continuous [TopologicalSpace Y] {g : Y -> Z} {f : X -> Y} (hg : IsLoc
allyConstant g) (hf : Continuous f) : IsLocallyConstant (g ∘ f)
参数：hg : IsLocallyConstant g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
-/
theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g)
    (hf : Continuous f) : IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf.isOpen_preimage _ (hg _)

/-- A locally constant function is constant on any preconnected set. -/
/-
**IsLocallyConstant.apply_eq_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
llyConstant`。
形式化陈述：apply_eq_of_isPreconnected {f : X -> Y} (hf : IsLocallyConstant f) {s : Se
t X} (hs : IsPreconnected s) {x y : X} (hx : x in s) (hy : y in s) : f x = f y
参数：hf : IsLocallyConstant f；hs : IsPreconnected s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
A locally constant function is constant on any preconnected set.
-/
theorem apply_eq_of_isPreconnected {f : X → Y} (hf : IsLocallyConstant f) {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  let U := f ⁻¹' {f y}
  suffices x ∉ Uᶜ from Classical.not_not.1 this
  intro hxV
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simp only [inter_empty, Set.not_nonempty_empty, inter_compl_self] at hs
/-
**IsLocallyConstant.apply_eq_of_preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocallyConstant`。
形式化陈述：apply_eq_of_preconnectedSpace [PreconnectedSpace X] {f : X -> Y} (hf : IsL
ocallyConstant f) (x y : X) : f x = f y
参数：hf : IsLocallyConstant f；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_isPreconnected`：apply_eq_of_isPreconnected
 {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x 
y : X} (hx : x in s) (hy : y in s)…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `trivial`：True
-/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (x y : X) : f x = f y :=
  hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
/-
**IsLocallyConstant.eq_const** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：eq_const [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x 
: X) : f = Function.const X (f x)
参数：hf : IsLocallyConstant f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocallyConstant.apply_eq_of_preconnectedSpace`：apply_eq_of_preconnecte
dSpace [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x y : X) :
 f x = f y
-/
theorem eq_const [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    f = Function.const X (f x) :=
  funext fun y => hf.apply_eq_of_preconnectedSpace y x
/-
**IsLocallyConstant.exists_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant
`。
形式化陈述：exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X -> Y} (hf : IsLo
callyConstant f) : exists y, f = Function.const X y
参数：hf : IsLocallyConstant f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocallyConstant.eq_const`：eq_const [PreconnectedSpace X] {f : X -> Y} 
(hf : IsLocallyConstant f) (x : X) : f = Function.const X (f x)
-/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X → Y} (hf : IsLocallyConstant f) :
    ∃ y, f = Function.const X y := by
  rcases isEmpty_or_nonempty X with h | h
  · exact ⟨Classical.arbitrary Y, funext <| h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩
/-
**IsLocallyConstant.iff_is_const** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：iff_is_const [PreconnectedSpace X] {f : X -> Y} : IsLocallyConstant f ↔ fo
rall x y, f x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_isPreconnected`：apply_eq_of_isPreconnected
 {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x 
y : X} (hx : x in s) (hy : y in s)…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `trivial`：True
· 使用定理 `IsLocallyConstant.of_constant`：of_constant (f : X -> Y) (h : forall x y,
 f x = f y) : IsLocallyConstant f
-/
theorem iff_is_const [PreconnectedSpace X] {f : X → Y} : IsLocallyConstant f ↔ ∀ x y, f x = f y :=
  ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩
/-
**IsLocallyConstant.range_finite** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：range_finite [CompactSpace X] {f : X -> Y} (hf : IsLocallyConstant f) : (S
et.range f).Finite
参数：hf : IsLocallyConstant f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discreteTopology_bot`：discreteTopology_bot (α : Type*) : @DiscreteTopolo
gy α ⊥
· 使用定理 `IsCompact.finite_of_discrete`：IsCompact.finite_of_discrete [DiscreteTopo
logy X] (hs : IsCompact s) : s.Finite
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `IsLocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocallyConstant
 f → Continuous f
-/
theorem range_finite [CompactSpace X] {f : X → Y} (hf : IsLocallyConstant f) :
    (Set.range f).Finite := by
  let : TopologicalSpace Y := ⊥; have := discreteTopology_bot Y
  exact (isCompact_range hf.continuous).finite_of_discrete

@[to_additive]
/-
**IsLocallyConstant.one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：one [One Y] : IsLocallyConstant (1 : X -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.const`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] (y : Y), IsLocallyConstant (Function.const X y)
-/
theorem one [One Y] : IsLocallyConstant (1 : X → Y) := IsLocallyConstant.const 1

@[to_additive]
/-
**IsLocallyConstant.inv** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：inv [Inv Y] ⦃f : X -> Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻
¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [
inst : TopologicalSpace X] {f : X → Y},   IsLocallyConstant f → ∀ (g : Y → Z), I
sLocallyCons…
-/
theorem inv [Inv Y] ⦃f : X → Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹ :=
  hf.comp fun x => x⁻¹

@[to_additive]
/-
**IsLocallyConstant.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：mul [Mul Y] ⦃f g : X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConst
ant g) : IsLocallyConstant (f * g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.comp₂`：comp₂ {Y₁ Y₂ Z : Type*} {f : X -> Y₁} {g : X ->
 Y₂} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : Y₁ -> Y₂ -> Z) :
 IsLocallyCon…
-/
theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f * g) :=
  hf.comp₂ hg (· * ·)

@[to_additive]
/-
**IsLocallyConstant.div** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：div [Div Y] ⦃f g : X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConst
ant g) : IsLocallyConstant (f / g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.comp₂`：comp₂ {Y₁ Y₂ Z : Type*} {f : X -> Y₁} {g : X ->
 Y₂} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : Y₁ -> Y₂ -> Z) :
 IsLocallyCon…
-/
theorem div [Div Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)

/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
/-
**IsLocallyConstant.desc** 是 Mathlib 中的一个定理，位于命名空间 `IsLocallyConstant`。
形式化陈述：desc {α β : Type*} (f : X -> α) (g : α -> β) (h : IsLocallyConstant (g ∘ f
)) (inj : Function.Injective g) : IsLocallyConstant f
参数：f : X -> α；g : α -> β；h : IsLocallyConstant (g ∘ f)；inj : Function.Injective 
g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s

--- 原说明 ---
If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`.
-/
theorem desc {α β : Type*} (f : X → α) (g : α → β) (h : IsLocallyConstant (g ∘ f))
    (inj : Function.Injective g) : IsLocallyConstant f := fun s => by
  rw [← preimage_image_eq s inj, preimage_preimage]
  exact h (g '' s)
/-
**IsLocallyConstant.of_constant_on_connected_components** 是 Mathlib 中的一个定理，位于命名空
间 `IsLocallyConstant`。
形式化陈述：of_constant_on_connected_components [LocallyConnectedSpace X] {f : X -> Y}
 (h : forall x, forall y in connectedComponent x, f y = f x) : IsLocallyConstant
 f
参数：h : forall x, forall y in connectedComponent x, f y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_exists_open`：iff_exists_open (f : X -> Y) : IsLoca
llyConstant f ↔ forall x, exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, 
f x' = f x
· 使用定理 `isOpen_connectedComponent`：isOpen_connectedComponent [LocallyConnectedSp
ace α] {x : α} : IsOpen (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem of_constant_on_connected_components [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ x, ∀ y ∈ connectedComponent x, f y = f x) : IsLocallyConstant f :=
  (iff_exists_open _).2 fun x =>
    ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩
/-
**IsLocallyConstant.of_constant_on_connected_clopens** 是 Mathlib 中的一个定理，位于命名空间 `
IsLocallyConstant`。
形式化陈述：of_constant_on_connected_clopens [LocallyConnectedSpace X] {f : X -> Y} (h
 : forall U : Set X, IsConnected U -> IsClopen U -> forall x in U, forall y in U
, f y = f x) : IsLocallyConstant f
参数：h : forall U : Set X, IsConnected U -> IsClopen U -> forall x in U, forall y 
in U, f y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.of_constant_on_connected_components`：of_constant_on_co
nnected_components [LocallyConnectedSpace X] {f : X -> Y} (h : forall x, forall 
y in connectedComponent x, f y = f x) : IsL…
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `isClopen_connectedComponent`：isClopen_connectedComponent [LocallyConnect
edSpace α] {x : α} : IsClopen (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem of_constant_on_connected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsConnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_components fun x =>
    h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent
/-
**IsLocallyConstant.of_constant_on_preconnected_clopens** 是 Mathlib 中的一个定理，位于命名空
间 `IsLocallyConstant`。
形式化陈述：of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X -> Y}
 (h : forall U : Set X, IsPreconnected U -> IsClopen U -> forall x in U, forall 
y in U, f y = f x) : IsLocallyConstant f
参数：h : forall U : Set X, IsPreconnected U -> IsClopen U -> forall x in U, forall
 y in U, f y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.of_constant_on_connected_clopens`：of_constant_on_conne
cted_clopens [LocallyConnectedSpace X] {f : X -> Y} (h : forall U : Set X, IsCon
nected U -> IsClopen U -> forall x in U,…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsPreconnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_clopens fun U hU ↦ h U hU.isPreconnected

end IsLocallyConstant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
/-
**LocallyConstant** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_5) → Type u_6 → [TopologicalSpace X] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (bundled) locally constant function from a topological space `X` to a type `Y`
.
-/
structure LocallyConstant (X Y : Type*) [TopologicalSpace X] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The map is locally constant. -/
  protected isLocallyConstant : IsLocallyConstant toFun

namespace LocallyConstant

/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const default⟩⟩
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (LocallyConstant X Y) X Y where
  coe := LocallyConstant.toFun
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

/-- See Note [custom simps projections]. -/
/-
**LocallyConstant.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant.Simps`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → LocallyCon
stant X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projections].
-/
def Simps.apply (f : LocallyConstant X Y) : X → Y := f

initialize_simps_projections LocallyConstant (toFun → apply)

@[simp]
/-
**LocallyConstant.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：toFun_eq_coe (f : LocallyConstant X Y) : f.toFun = f
参数：f : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : LocallyConstant X Y) : f.toFun = f :=
  rfl

@[simp]
/-
**LocallyConstant.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_mk (f : X -> Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f
参数：f : X -> Y；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl
/-
**LocallyConstant.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] {f g : Locally
Constant X Y}, f = g → ∀ (x : X), f x = g x
参数：x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : LocallyConstant X Y} (h : f = g) (x : X) : f x = g x :=
  DFunLike.congr_fun h x
/-
**LocallyConstant.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] (f : LocallyCo
nstant X Y) {x y : X}, x = y → f x = f y
参数：f : LocallyConstant X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (f : LocallyConstant X Y) {x y : X} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
/-
**LocallyConstant.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_injective : @Function.Injective (LocallyConstant X Y) (X -> Y) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X → Y) (↑) := fun _ _ =>
  DFunLike.ext'

@[norm_cast]
/-
**LocallyConstant.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_inj {f g : LocallyConstant X Y} : (f : X -> Y) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LocallyConstant.coe_injective`：coe_injective : @Function.Injective (Loca
llyConstant X Y) (X -> Y) (↑)
-/
theorem coe_inj {f g : LocallyConstant X Y} : (f : X → Y) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/-
**LocallyConstant.ext** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

section CodomainTopologicalSpace

variable [TopologicalSpace Y] (f : LocallyConstant X Y)

/-
**LocallyConstant.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : LocallyConstant X Y),   Continuous ⇑f
参数：f : LocallyConstant X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocallyConstant
 f → Continuous f
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
-/
protected theorem continuous : Continuous f :=
  f.isLocallyConstant.continuous

/-- We can turn a locally-constant function into a bundled `ContinuousMap`. -/
/-
**LocallyConstant.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → LocallyConstant X Y → C(X, Y)
参数：X, Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : LocallyConstant X Y),   Conti
nuous ⇑f

--- 原说明 ---
We can turn a locally-constant function into a bundled `ContinuousMap`.
-/
@[coe] def toContinuousMap : C(X, Y) :=
  ⟨f, f.continuous⟩

/-- As a shorthand, `LocallyConstant.toContinuousMap` is available as a coercion -/
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a shorthand, `LocallyConstant.toContinuousMap` is available as a coercion
-/
instance : Coe (LocallyConstant X Y) C(X, Y) := ⟨toContinuousMap⟩
/-
**LocallyConstant.coe_continuousMap** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : LocallyConstant X Y),   ⇑↑f = ⇑f
参数：f : LocallyConstant X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_continuousMap : ((f : C(X, Y)) : X → Y) = (f : X → Y) := rfl
/-
**LocallyConstant.toContinuousMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LocallyCo
nstant`。
形式化陈述：toContinuousMap_injective : Function.Injective (toContinuousMap : LocallyC
onstant X Y -> C(X, Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
-/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : LocallyConstant X Y → C(X, Y)) := fun _ _ h =>
  ext (ContinuousMap.congr_fun h)

end CodomainTopologicalSpace

/-- The constant locally constant function on `X` with value `y : Y`. -/
/-
**LocallyConstant.const** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConsta
nt X Y
参数：X : Type*；y : Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.const`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] (y : Y), IsLocallyConstant (Function.const X y)

--- 原说明 ---
The constant locally constant function on `X` with value `y : Y`.
-/
def const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]
/-
**LocallyConstant.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_const (y : Y) : (const X y : X -> Y) = Function.const X y
参数：y : Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (y : Y) : (const X y : X → Y) = Function.const X y :=
  rfl

/-- Evaluation/projection as a locally constant function. -/
@[simps]
/-
**LocallyConstant.eval** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：eval {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] (i : 
ι) [DiscreteTopology (X i)] : LocallyConstant (Π i, X i) (X i) where toFun
参数：X i；i : ι；X i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation/projection as a locally constant function.
-/
def eval {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (i : ι) [DiscreteTopology (X i)] :
    LocallyConstant (Π i, X i) (X i) where
  toFun := fun f ↦ f i
  isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr <| continuous_apply i

/-- The locally constant function to `Fin 2` associated to a clopen set. -/
/-
**LocallyConstant.ofIsClopen** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：ofIsClopen {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidab
le (x in U)] (hU : IsClopen U) : LocallyConstant X (Fin 2) where toFun x
参数：x in U；hU : IsClopen U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The locally constant function to `Fin 2` associated to a clopen set.
-/
def ofIsClopen {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : LocallyConstant X (Fin 2) where
  toFun x := if x ∈ U then 0 else 1
  isLocallyConstant := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 <| Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · convert! hU.2 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw [← isClosed_compl_iff]
      convert! hU.1
      ext
      simp

@[simp]
/-
**LocallyConstant.ofIsClopen_fiber_zero** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConsta
nt`。
形式化陈述：ofIsClopen_fiber_zero {X : Type*} [TopologicalSpace X] {U : Set X} [forall
 x, Decidable (x in U)] (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({0} : Set (Fin 2)
) = U
参数：x in U；hU : IsClopen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem ofIsClopen_fiber_zero {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({0} : Set (Fin 2)) = U := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto

@[simp]
/-
**LocallyConstant.ofIsClopen_fiber_one** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstan
t`。
形式化陈述：ofIsClopen_fiber_one {X : Type*} [TopologicalSpace X] {U : Set X} [forall 
x, Decidable (x in U)] (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({1} : Set (Fin 2))
 = Uᶜ
参数：x in U；hU : IsClopen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofIsClopen_fiber_one {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({1} : Set (Fin 2)) = Uᶜ := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]
/-
**LocallyConstant.locallyConstant_eq_of_fiber_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 
`LocallyConstant`。
形式化陈述：locallyConstant_eq_of_fiber_zero_eq {X : Type*} [TopologicalSpace X] (f g 
: LocallyConstant X (Fin 2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g
参数：f g : LocallyConstant X (Fin 2)；h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `Fin.fin_two_eq_of_eq_zero_iff`：∀ {a b : Fin 2}, (a = 0 ↔ b = 0) → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem locallyConstant_eq_of_fiber_zero_eq {X : Type*} [TopologicalSpace X]
    (f g : LocallyConstant X (Fin 2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g := by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)
/-
**LocallyConstant.range_finite** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.range f).Fi
nite
参数：f : LocallyConstant X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.range_finite`：range_finite [CompactSpace X] {f : X -> 
Y} (hf : IsLocallyConstant f) : (Set.range f).Finite
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
-/
theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.range f).Finite :=
  f.isLocallyConstant.range_finite
/-
**LocallyConstant.apply_eq_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `LocallyC
onstant`。
形式化陈述：apply_eq_of_isPreconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsP
reconnected s) {x y : X} (hx : x in s) (hy : y in s) : f x = f y
参数：f : LocallyConstant X Y；hs : IsPreconnected s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_isPreconnected`：apply_eq_of_isPreconnected
 {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x 
y : X} (hx : x in s) (hy : y in s)…
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
-/
theorem apply_eq_of_isPreconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy
/-
**LocallyConstant.apply_eq_of_preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Local
lyConstant`。
形式化陈述：apply_eq_of_preconnectedSpace [PreconnectedSpace X] (f : LocallyConstant X
 Y) (x y : X) : f x = f y
参数：f : LocallyConstant X Y；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_isPreconnected`：apply_eq_of_isPreconnected
 {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x 
y : X} (hx : x in s) (hy : y in s)…
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `trivial`：True
-/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) :
    f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
/-
**LocallyConstant.eq_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = con
st X (f x)
参数：f : LocallyConstant X Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `LocallyConstant.apply_eq_of_preconnectedSpace`：apply_eq_of_preconnectedS
pace [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) : f x = f y
-/
theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext fun _ => apply_eq_of_preconnectedSpace f _ _
/-
**LocallyConstant.exists_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X 
Y) : exists y, f = const X y
参数：f : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LocallyConstant.eq_const`：eq_const [PreconnectedSpace X] (f : LocallyCon
stant X Y) (x : X) : f = const X (f x)
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
-/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) :
    ∃ y, f = const X y := by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩

/-- Push forward of locally constant maps under any map, by post-composition. -/
/-
**LocallyConstant.map** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：map (f : Y -> Z) (g : LocallyConstant X Y) : LocallyConstant X Z
参数：f : Y -> Z；g : LocallyConstant X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward of locally constant maps under any map, by post-composition.
-/
def map (f : Y → Z) (g : LocallyConstant X Y) : LocallyConstant X Z :=
  ⟨f ∘ g, g.isLocallyConstant.comp f⟩

@[simp]
/-
**LocallyConstant.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：map_apply (f : Y -> Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g
参数：f : Y -> Z；g : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (f : Y → Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g :=
  rfl

@[simp]
/-
**LocallyConstant.map_id** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：map_id : @map X Y Y _ id = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : @map X Y Y _ id = id := rfl

@[simp]
/-
**LocallyConstant.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂) : @map X _ _ _ g
 ∘ map f = map (g ∘ f)
参数：g : Y₂ -> Y₃；f : Y₁ -> Y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
    @map X _ _ _ g ∘ map f = map (g ∘ f) := rfl

/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
/-
**LocallyConstant.flip** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：flip {X α β : Type*} [TopologicalSpace X] (f : LocallyConstant X (α -> β))
 (a : α) : LocallyConstant X β
参数：f : LocallyConstant X (α -> β)；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a locally constant function to `α → β`, construct a family of locally cons
tant
functions with values in β indexed by α.
-/
def flip {X α β : Type*} [TopologicalSpace X] (f : LocallyConstant X (α → β)) (a : α) :
    LocallyConstant X β :=
  f.map fun f => f a

/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
/-
**LocallyConstant.unflip** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：unflip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α -> LocallyCo
nstant X β) : LocallyConstant X (α -> β) where toFun x a
参数：f : α -> LocallyConstant X β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α.
-/
def unflip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
    LocallyConstant X (α → β) where
  toFun x a := f a x
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by
      ext; simp [funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _

@[simp]
/-
**LocallyConstant.unflip_flip** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：unflip_flip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : LocallyCo
nstant X (α -> β)) : unflip f.flip = f
参数：f : LocallyConstant X (α -> β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unflip_flip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : LocallyConstant X (α → β)) : unflip f.flip = f := rfl

@[simp]
/-
**LocallyConstant.flip_unflip** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：flip_unflip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α -> Loca
llyConstant X β) : (unflip f).flip = f
参数：f : α -> LocallyConstant X β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_unflip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : α → LocallyConstant X β) : (unflip f).flip = f := rfl

section Comap

variable [TopologicalSpace Y]

/-- Pull back of locally constant maps under a continuous map, by pre-composition. -/
/-
**LocallyConstant.comap** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z
参数：f : C(X, Y)；g : LocallyConstant Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back of locally constant maps under a continuous map, by pre-composition.
-/
def comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z :=
  ⟨g ∘ f, g.isLocallyConstant.comp_continuous f.continuous⟩

@[simp]
/-
**LocallyConstant.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_comap (f : C(X, Y)) (g : LocallyConstant Y Z) : (comap f g) = g ∘ f
参数：f : C(X, Y)；g : LocallyConstant Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (f : C(X, Y)) (g : LocallyConstant Y Z) :
    (comap f g) = g ∘ f := rfl
/-
**LocallyConstant.coe_comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_comap_apply (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X) : comap f 
g x = g (f x)
参数：f : C(X, Y)；g : LocallyConstant Y Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap_apply (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X) :
    comap f g x = g (f x) := rfl

@[simp]
/-
**LocallyConstant.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：comap_id : comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id : comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z) := rfl
/-
**LocallyConstant.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：comap_comp {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y)) : 
comap (Z
参数：f : C(W, X)；g : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y)) :
    comap (Z := Z) (g.comp f) = comap f ∘ comap g := rfl
/-
**LocallyConstant.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：comap_comap {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y)) (
x : LocallyConstant Y Z) : comap f (comap g x) = comap (g.comp f) x
参数：f : C(W, X)；g : C(X, Y)；x : LocallyConstant Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
    (x : LocallyConstant Y Z) : comap f (comap g x) = comap (g.comp f) x := rfl
/-
**LocallyConstant.comap_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：comap_const (f : C(X, Y)) (y : Y) (h : forall x, f x = y) : (comap f : Loc
allyConstant Y Z -> LocallyConstant X Z) = fun g => const X (g y)
参数：f : C(X, Y)；y : Y；h : forall x, f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_const (f : C(X, Y)) (y : Y) (h : ∀ x, f x = y) :
    (comap f : LocallyConstant Y Z → LocallyConstant X Z) = fun g => const X (g y) := by
  ext; simp [h]
/-
**LocallyConstant.comap_injective** 是 Mathlib 中的一个引理，位于命名空间 `LocallyConstant`。
形式化陈述：comap_injective (f : C(X, Y)) (hfs : f.1.Surjective) : (comap (Z
参数：f : C(X, Y)；hfs : f.1.Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocallyConstant.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] {f g : LocallyConstant X Y}, f = g → ∀ (x : X), f x = g x
-/
lemma comap_injective (f : C(X, Y)) (hfs : f.1.Surjective) :
    (comap (Z := Z) f).Injective := by
  intro a b h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  simpa [← hx] using LocallyConstant.congr_fun h x

end Comap

section Desc

/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
/-
**LocallyConstant.desc** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：desc {X α β : Type*} [TopologicalSpace X] {g : α -> β} (f : X -> α) (h : L
ocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) : LocallyCon
stant X α where toFun
参数：f : X -> α；h : LocallyConstant X β；cond : g ∘ f = h；inj : Function.Injective 
g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a locally constant function factors through an injection, then it factors thr
ough a locally
constant function.
-/
def desc {X α β : Type*} [TopologicalSpace X] {g : α → β} (f : X → α) (h : LocallyConstant X β)
    (cond : g ∘ f = h) (inj : Function.Injective g) : LocallyConstant X α where
  toFun := f
  isLocallyConstant := IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj

@[simp]
/-
**LocallyConstant.coe_desc** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_desc {X α β : Type*} [TopologicalSpace X] (f : X -> α) (g : α -> β) (h
 : LocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) : ⇑(desc
 f h cond inj) = f
参数：f : X -> α；g : α -> β；h : LocallyConstant X β；cond : g ∘ f = h；inj : Function
.Injective g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_desc {X α β : Type*} [TopologicalSpace X] (f : X → α) (g : α → β)
    (h : LocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) :
    ⇑(desc f h cond inj) = f :=
  rfl

end Desc

section Indicator

variable {R : Type*} [One R] {U : Set X} (f : LocallyConstant X R)

/-- Given a clopen set `U` and a locally constant function `f`, `LocallyConstant.mulIndicator`
  returns the locally constant function that is `f` on `U` and `1` otherwise. -/
@[to_additive (attr := simps) /-- Given a clopen set `U` and a locally constant function `f`,
  `LocallyConstant.indicator` returns the locally constant function that is `f` on `U` and `0`
  otherwise. -/]
/-
**LocallyConstant.mulIndicator** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：mulIndicator (hU : IsClopen U) : LocallyConstant X R where toFun
参数：hU : IsClopen U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulIndicator (hU : IsClopen U) : LocallyConstant X R where
  toFun := Set.mulIndicator U f
  isLocallyConstant := fun s => by
    rw [mulIndicator_preimage, Set.ite, Set.sdiff_eq]
    exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)

variable (a : X)

open scoped Classical in
@[to_additive]
/-
**LocallyConstant.mulIndicator_apply_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `LocallyCon
stant`。
形式化陈述：mulIndicator_apply_eq_if (hU : IsClopen U) : mulIndicator f hU a = if a in
 U then f a else 1
参数：hU : IsClopen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply`：mulIndicator_apply (s : Set α) (f : α -> M) (a :
 α) [Decidable (a in s)] : mulIndicator s f a = if a in s then f a else 1
-/
theorem mulIndicator_apply_eq_if (hU : IsClopen U) :
    mulIndicator f hU a = if a ∈ U then f a else 1 :=
  Set.mulIndicator_apply U f a

variable {a}

@[to_additive]
/-
**LocallyConstant.mulIndicator_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant
`。
形式化陈述：mulIndicator_of_mem (hU : IsClopen U) (h : a in U) : f.mulIndicator hU a =
 f a
参数：hU : IsClopen U；h : a in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
-/
theorem mulIndicator_of_mem (hU : IsClopen U) (h : a ∈ U) : f.mulIndicator hU a = f a :=
  Set.mulIndicator_of_mem h _

@[to_additive]
/-
**LocallyConstant.mulIndicator_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConst
ant`。
形式化陈述：mulIndicator_of_notMem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a
 = 1
参数：hU : IsClopen U；h : a ∉ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
-/
theorem mulIndicator_of_notMem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 :=
  Set.mulIndicator_of_notMem h _

end Indicator

section Equiv

/--
The equivalence between `LocallyConstant X Z` and `LocallyConstant Y Z` given a
homeomorphism `X ≃ₜ Y`
-/
@[simps]
/-
**LocallyConstant.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ Locall
yConstant Y Z where toFun
参数：e : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `LocallyConstant X Z` and `LocallyConstant Y Z` given a
homeomorphism `X ≃ₜ Y`
-/
def congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z where
  toFun := comap e.symm
  invFun := comap e
  left_inv := by
    intro
    simp [comap_comap]
  right_inv := by
    intro
    simp [comap_comap]

/--
The equivalence between `LocallyConstant X Y` and `LocallyConstant X Z` given an
equivalence `Y ≃ Z`
-/
@[simps]
/-
**LocallyConstant.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where t
oFun
参数：e : Y ≃ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between `LocallyConstant X Y` and `LocallyConstant X Z` given an
equivalence `Y ≃ Z`
-/
def congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where
  toFun := map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

variable (X) in
/--
The set of clopen subsets of a topological space is equivalent to the locally constant maps to
a two-element set
-/
/-
**LocallyConstant.equivClopens** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：equivClopens [forall (s : Set X) x, Decidable (x in s)] : LocallyConstant 
X (Fin 2) ≃ TopologicalSpace.Clopens X where toFun f
参数：s : Set X；x in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier

--- 原说明 ---
The set of clopen subsets of a topological space is equivalent to the locally co
nstant maps to
a two-element set
-/
def equivClopens [∀ (s : Set X) x, Decidable (x ∈ s)] :
    LocallyConstant X (Fin 2) ≃ TopologicalSpace.Clopens X where
  toFun f := ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  invFun s := ofIsClopen s.2
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp

end Equiv

section Piecewise

/-- Given two closed sets covering a topological space, and locally constant maps on these two sets,
then if these two locally constant maps agree on the intersection, we get a piecewise defined
locally constant map on the whole space.

TODO: Generalise this construction to `ContinuousMap`. -/
/-
**LocallyConstant.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ un
ion C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z) (hfg : 
forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩) [DecidablePre
d (· in C₁)] : LocallyConstant X Z where toFun i
参数：h₁ : IsClosed C₁；h₂ : IsClosed C₂；h : C₁ union C₂ = Set.univ；f : LocallyConst
ant C₁ Z；g : LocallyConstant C₂ Z；hfg : forall (x : X) (hx : x in C₁ inter C₂), 
f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩；· in C₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two closed sets covering a topological space, and locally constant maps on
 these two sets,
then if these two locally constant maps agree on the intersection, we get a piec
ewise defined
locally constant map on the whole space.

TODO: Generalise this construction to `ContinuousMap`.
-/
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] : LocallyConstant X Z where
  toFun i := if hi : i ∈ C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    have : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
    dsimp only [coe_mk]
    rw [Set.union_eq_iUnion] at h
    refine (locallyFinite_of_finite _).continuous h (fun i ↦ ?_) (fun i ↦ ?_)
    · cases i <;> [exact h₂; exact h₁]
    · cases i <;> rw [continuousOn_iff_continuous_domRestrict]
      · convert! hg
        ext x
        simp only [cond_false, domRestrict_apply, Subtype.coe_eta, dite_eq_right_iff]
        exact fun hx ↦ hfg x ⟨hx, x.prop⟩
      · simp only [cond_true, domRestrict_dite, Subtype.coe_eta]
        exact hf

@[simp]
/-
**LocallyConstant.piecewise_apply_left** 是 Mathlib 中的一个引理，位于命名空间 `LocallyConstan
t`。
形式化陈述：piecewise_apply_left {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
 (h : C₁ union C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂
 Z) (hfg : forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩) [D
ecidablePred (· in C₁)] (x : X) (hx : x in C₁) : piecewise h₁ h₂ h f g hfg x = f
 ⟨x, hx⟩
参数：h₁ : IsClosed C₁；h₂ : IsClosed C₂；h : C₁ union C₂ = Set.univ；f : LocallyConst
ant C₁ Z；g : LocallyConstant C₂ Z；hfg : forall (x : X) (hx : x in C₁ inter C₂), 
f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩；· in C₁；x : X；hx : x in C₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma piecewise_apply_left {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] (x : X) (hx : x ∈ C₁) :
    piecewise h₁ h₂ h f g hfg x = f ⟨x, hx⟩ := by
  simp only [piecewise,
    coe_mk]
  rw [dif_pos hx]

@[simp]
/-
**LocallyConstant.piecewise_apply_right** 是 Mathlib 中的一个引理，位于命名空间 `LocallyConsta
nt`。
形式化陈述：piecewise_apply_right {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂
) (h : C₁ union C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C
₂ Z) (hfg : forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩) [
DecidablePred (· in C₁)] (x : X) (hx : x in C₂) : piecewise h₁ h₂ h f g hfg x = 
g ⟨x, hx⟩
参数：h₁ : IsClosed C₁；h₂ : IsClosed C₂；h : C₁ union C₂ = Set.univ；f : LocallyConst
ant C₁ Z；g : LocallyConstant C₂ Z；hfg : forall (x : X) (hx : x in C₁ inter C₂), 
f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩；· in C₁；x : X；hx : x in C₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma piecewise_apply_right {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] (x : X) (hx : x ∈ C₂) :
    piecewise h₁ h₂ h f g hfg x = g ⟨x, hx⟩ := by
  simp only [piecewise,
    coe_mk]
  split_ifs with h
  · exact hfg x ⟨h, hx⟩
  · rfl

/-- A variant of `LocallyConstant.piecewise` where the two closed sets cover a subset.

TODO: Generalise this construction to `ContinuousMap`. -/
/-
**LocallyConstant.piecewise'** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：piecewise' {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClose
d C₁) (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
 [DecidablePred (· in C₁)] (hf : forall x (hx : x in C₁ inter C₂), f₁ ⟨x, hx.1⟩ 
= f₂ ⟨x, hx.2⟩) : LocallyConstant C₀ Z
参数：h₀ : C₀ subseteq C₁ union C₂；h₁ : IsClosed C₁；h₂ : IsClosed C₂；f₁ : LocallyCo
nstant C₁ Z；f₂ : LocallyConstant C₂ Z；· in C₁；hf : forall x (hx : x in C₁ inter 
C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `LocallyConstant.piecewise` where the two closed sets cover a subse
t.

TODO: Generalise this construction to `ContinuousMap`.
-/
def piecewise' {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩) :
    LocallyConstant C₀ Z :=
  letI : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
    (by simpa [eq_univ_iff_forall] using! h₀)
    (f₁.comap ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩)
    (f₂.comap ⟨(restrictPreimage C₂ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩) <| by
      rintro ⟨x, hx₀⟩ ⟨hx₁ : x ∈ C₁, hx₂ : x ∈ C₂⟩
      simpa using hf x ⟨hx₁, hx₂⟩

@[simp]
/-
**LocallyConstant.piecewise'_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConsta
nt`。
形式化陈述：∀ {X : Type u_1} {Z : Type u_3} [inst : TopologicalSpace X] {C₀ C₁ C₂ : Se
t X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)   (h₂ : IsClosed C₂) (f₁ : LocallyCo
nstant (↑C₁) Z) (f₂ : LocallyConstant (↑C₂) Z)   [inst_1 : DecidablePred fun x =
> x ∈ C₁] (hf : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, ⋯⟩ = f₂ ⟨x, ⋯⟩) (x : ↑C₀)  
 (hx : ↑x ∈ C₁), (LocallyConstant.piecewise' h₀ h₁ h₂ f₁ f₂ hf) x = f₁ ⟨↑x, hx⟩
参数：h₀ : C₀ ⊆ C₁ ∪ C₂；h₁ : IsClosed C₁；h₂ : IsClosed C₂；f₁ : LocallyConstant (↑C₁
) Z；f₂ : LocallyConstant (↑C₂) Z；hf : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, ⋯⟩ = 
f₂ ⟨x, ⋯⟩；x : ↑C₀；hx : ↑x ∈ C₁；LocallyConstant.piecewise' h₀ h₁ h₂ f₁ f₂ hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocallyConstant.piecewise'.eq_1`：∀ {X : Type u_1} {Z : Type u_3} [inst :
 TopologicalSpace X] {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)  
 (h₂ : IsClosed C₂) (…
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `LocallyConstant.piecewise_apply_left`：piecewise_apply_left {C₁ C₂ : Set 
X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ union C₂ = Set.univ) (f : Local
lyConstant C₁ Z) (g : Loca…
-/
lemma piecewise'_apply_left {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val ∈ C₁) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₁ ⟨x.val, hx⟩ := by
  let : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  rw [piecewise', piecewise_apply_left (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

@[simp]
/-
**LocallyConstant.piecewise'_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConst
ant`。
形式化陈述：∀ {X : Type u_1} {Z : Type u_3} [inst : TopologicalSpace X] {C₀ C₁ C₂ : Se
t X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)   (h₂ : IsClosed C₂) (f₁ : LocallyCo
nstant (↑C₁) Z) (f₂ : LocallyConstant (↑C₂) Z)   [inst_1 : DecidablePred fun x =
> x ∈ C₁] (hf : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, ⋯⟩ = f₂ ⟨x, ⋯⟩) (x : ↑C₀)  
 (hx : ↑x ∈ C₂), (LocallyConstant.piecewise' h₀ h₁ h₂ f₁ f₂ hf) x = f₂ ⟨↑x, hx⟩
参数：h₀ : C₀ ⊆ C₁ ∪ C₂；h₁ : IsClosed C₁；h₂ : IsClosed C₂；f₁ : LocallyConstant (↑C₁
) Z；f₂ : LocallyConstant (↑C₂) Z；hf : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, ⋯⟩ = 
f₂ ⟨x, ⋯⟩；x : ↑C₀；hx : ↑x ∈ C₂；LocallyConstant.piecewise' h₀ h₁ h₂ f₁ f₂ hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocallyConstant.piecewise'.eq_1`：∀ {X : Type u_1} {Z : Type u_3} [inst :
 TopologicalSpace X] {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)  
 (h₂ : IsClosed C₂) (…
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `LocallyConstant.piecewise_apply_right`：piecewise_apply_right {C₁ C₂ : Se
t X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ union C₂ = Set.univ) (f : Loc
allyConstant C₁ Z) (g : Loc…
-/
lemma piecewise'_apply_right {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val ∈ C₂) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₂ ⟨x.val, hx⟩ := by
  let : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  rw [piecewise', piecewise_apply_right (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

end Piecewise

end LocallyConstant

