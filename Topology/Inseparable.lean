/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury Kudryashov
-/
module

public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.Fibration
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Inseparable points in a topological space

In this file we prove basic properties of the following notions defined elsewhere.

* `Specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `Inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `InseparableSetoid X`: same relation, as a `Setoid`;

* `SeparationQuotient X`: the quotient of `X` by its `InseparableSetoid`.

We also prove various basic properties of the relation `Inseparable`.

## Notation

- `x ⤳ y`: notation for `Specializes x y`;
- `x ~ᵢ y` is used as a local notation for `Inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/

@[expose] public section


open Set Filter Function Topology

variable {X Y Z α ι : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (A i)] {x y z : X} {s : Set X} {f g : X → Y}

/-!
### `Specializes` relation
-/

/-- A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
below. -/
/-
**specializes_TFAE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x <= 𝓝 y, forall s : S
et X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClosed s -> x in s -> y 
in s, y in closure ({ x } : Set X), closure ({ y } : Set X) subseteq closure { x
 }, ClusterPt y (pure x)]
参数：x y : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
A collection of equivalent definitions of `x ⤳ y`. The public API is given by `i
ff` lemmas
below.
-/
theorem specializes_TFAE (x y : X) :
    List.TFAE [x ⤳ y,
      pure x ≤ 𝓝 y,
      ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s,
      ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s,
      y ∈ closure ({ x } : Set X),
      closure ({ y } : Set X) ⊆ closure { x },
      ClusterPt y (pure x)] := by
  tfae_have 1 → 2 := (pure_le_nhds _).trans
  tfae_have 2 → 3 := fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 → 4 := fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 → 5 := fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5 := isClosed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7 := by
    rw [mem_closure_iff_clusterPt, principal_singleton]
  tfae_have 5 → 1 := by
    refine fun h => (nhds_basis_opens _).ge_iff.2 ?_
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish
/-
**specializes_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_nhds : x ⤳ y ↔ 𝓝 x <= 𝓝 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl
/-
**Specializes.not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoint (𝓝 x) (𝓝 y)
参数：h : x ⤳ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoint (𝓝 x) (𝓝 y) := fun hd ↦
  absurd (hd.mono_right h) <| by simp [NeBot.ne']
/-
**specializes_iff_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure
/-
**ker_nhds_eq_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ x} := by
  ext; simp [specializes_iff_pure, le_def]
/-
**specializes_iff_forall_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_forall_open : x ⤳ y ↔ forall s : Set X, IsOpen s -> y in s
 -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_TFAE x y).out 0 2

omit [TopologicalSpace X] in
/-
**Tendsto.specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Tendsto.specializes {l : Filter X} {y : Y} (h : Tendsto g l (𝓝 y)) (hl : f
orall x, f x ⤳ g x) : Tendsto f l (𝓝 y)
参数：h : Tendsto g l (𝓝 y)；hl : forall x, f x ⤳ g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Tendsto.specializes {l : Filter X} {y : Y} (h : Tendsto g l (𝓝 y)) (hl : ∀ x, f x ⤳ g x) :
    Tendsto f l (𝓝 y) := by
  simp_all only [specializes_iff_forall_open, tendsto_nhds]
  refine fun s ho hy => mem_of_superset (h s ho hy) fun x hx => ?_
  exact mem_preimage.2 (hl x s ho (mem_preimage.1 hx))
/-
**Specializes.mem_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y in s) : x in s
参数：h : x ⤳ y；hs : IsOpen s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `specializes_iff_forall_open`：specializes_iff_forall_open : x ⤳ y ↔ foral
l s : Set X, IsOpen s -> y in s -> x in s
-/
theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy
/-
**IsOpen.not_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y in s) : ¬x ⤳ y
参数：hs : IsOpen s；hx : x ∉ s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
-/
theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h =>
  hx <| h.mem_open hs hy
/-
**specializes_iff_forall_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_forall_closed : x ⤳ y ↔ forall s : Set X, IsClosed s -> x 
in s -> y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_TFAE x y).out 0 3
/-
**Specializes.mem_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x in s) : y in 
s
参数：h : x ⤳ y；hs : IsClosed s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `specializes_iff_forall_closed`：specializes_iff_forall_closed : x ⤳ y ↔ f
orall s : Set X, IsClosed s -> x in s -> y in s
-/
theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx
/-
**IsClosed.not_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.not_specializes (hs : IsClosed s) (hx : x in s) (hy : y ∉ s) : ¬x
 ⤳ y
参数：hs : IsClosed s；hx : x in s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_closed`：Specializes.mem_closed (h : x ⤳ y) (hs : IsClose
d s) (hx : x in s) : y in s
-/
theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx
/-
**specializes_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_mem_closure : x ⤳ y ↔ y in closure ({x} : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : Set X) :=
  (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure
/-
**specializes_iff_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) subseteq cl
osure {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) ⊆ closure {x} :=
  (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset
/-
**specializes_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_clusterPt : x ⤳ y ↔ ClusterPt y (pure x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `specializes_TFAE`：specializes_TFAE (x y : X) : List.TFAE [x ⤳ y, pure x 
<= 𝓝 y, forall s : Set X, IsOpen s -> y in s -> x in s, forall s : Set X, IsClos
ed s -…
-/
theorem specializes_iff_clusterPt : x ⤳ y ↔ ClusterPt y (pure x) :=
  (specializes_TFAE x y).out 0 6
/-
**Filter.HasBasis.specializes_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.specializes_iff {ι} {p : ι -> Prop} {s : ι -> Set X} (h : 
(𝓝 y).HasBasis p s) : x ⤳ y ↔ forall i, p i -> x in s i
参数：h : (𝓝 y).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `specializes_iff_pure`：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
-/
theorem Filter.HasBasis.specializes_iff {ι} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
  specializes_iff_pure.trans h.ge_iff
/-
**specializes_rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_rfl : x ⤳ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem specializes_rfl : x ⤳ x := le_rfl

@[refl]
/-
**specializes_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_refl (x : X) : x ⤳ x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_rfl`：specializes_rfl : x ⤳ x
-/
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl

@[trans]
/-
**Specializes.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.trans : x ⤳ y -> y ⤳ z -> x ⤳ z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
  le_trans
/-
**specializes_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_of_eq (e : x = y) : x ⤳ y
参数：e : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
-/
theorem specializes_of_eq (e : x = y) : x ⤳ y :=
  e ▸ specializes_refl x

alias Specializes.of_eq := specializes_of_eq
/-
**specializes_of_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_of_nhdsWithin (h₁ : 𝓝[s] x <= 𝓝[s] y) (h₂ : x in s) : x ⤳ y
参数：h₁ : 𝓝[s] x <= 𝓝[s] y；h₂ : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_iff_pure`：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem specializes_of_nhdsWithin (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
  specializes_iff_pure.2 <|
    calc
      pure x ≤ 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ ≤ 𝓝[s] y := h₁
      _ ≤ 𝓝 y := inf_le_left
/-
**Specializes.map_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.map_of_continuousWithinAt {s : Set X} (h : x ⤳ y) (hf : Contin
uousWithinAt f s y) (hx : x in s) : f x ⤳ f y
参数：h : x ⤳ y；hf : ContinuousWithinAt f s y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `specializes_iff_pure`：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.pure_le_principal`：pure_le_principal {s : Set α} (a : α) : pure a
 <= 𝓟 s ↔ a in s
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
-/
theorem Specializes.map_of_continuousWithinAt {s : Set X} (h : x ⤳ y)
    (hf : ContinuousWithinAt f s y) (hx : x ∈ s) : f x ⤳ f y := by
  rw [specializes_iff_pure] at h ⊢
  calc pure (f x)
    _ = map f (pure x) := (map_pure f x).symm
    _ ≤ map f (𝓝 y ⊓ 𝓟 s) := map_mono (le_inf h ((pure_le_principal x).mpr hx))
    _ = map f (𝓝[s] y) := rfl
    _ ≤ _ := hf.tendsto
/-
**Specializes.map_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.map_of_continuousOn {s : Set X} (h : x ⤳ y) (hf : ContinuousOn
 f s) (hx : x in s) (hy : y in s) : f x ⤳ f y
参数：h : x ⤳ y；hf : ContinuousOn f s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map_of_continuousWithinAt`：Specializes.map_of_continuousWith
inAt {s : Set X} (h : x ⤳ y) (hf : ContinuousWithinAt f s y) (hx : x in s) : f x
 ⤳ f y
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
-/
theorem Specializes.map_of_continuousOn {s : Set X} (h : x ⤳ y)
    (hf : ContinuousOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ⤳ f y :=
  h.map_of_continuousWithinAt (hf.continuousWithinAt hy) hx
/-
**Specializes.map_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.map_of_continuousAt (h : x ⤳ y) (hf : ContinuousAt f y) : f x 
⤳ f y
参数：h : x ⤳ y；hf : ContinuousAt f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map_of_continuousWithinAt`：Specializes.map_of_continuousWith
inAt {s : Set X} (h : x ⤳ y) (hf : ContinuousWithinAt f s y) (hx : x in s) : f x
 ⤳ f y
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem Specializes.map_of_continuousAt (h : x ⤳ y) (hf : ContinuousAt f y) : f x ⤳ f y :=
  h.map_of_continuousWithinAt hf.continuousWithinAt (mem_univ x)
/-
**Specializes.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y
参数：h : x ⤳ y；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map_of_continuousAt`：Specializes.map_of_continuousAt (h : x 
⤳ y) (hf : ContinuousAt f y) : f x ⤳ f y
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuousAt hf.continuousAt
/-
**Topology.IsInducing.specializes_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.specializes_iff (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ 
y
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Topology.IsInducing.specializes_iff (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]
/-
**subtype_specializes_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtype_specializes_iff {p : X -> Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X
) ⤳ y
参数：x y : Subtype p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
theorem subtype_specializes_iff {p : X → Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  IsInducing.subtypeVal.specializes_iff.symm

@[simp]
/-
**specializes_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧
 y₁ ⤳ y₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ := by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]
/-
**Specializes.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) : (
x₁, y₁) ⤳ (x₂, y₂)
参数：hx : x₁ ⤳ x₂；hy : y₁ ⤳ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_prod`：specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ 
(x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂
-/
theorem Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
    (x₁, y₁) ⤳ (x₂, y₂) :=
  specializes_prod.2 ⟨hx, hy⟩
/-
**Specializes.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.fst {a b : X × Y} (h : a ⤳ b) : a.1 ⤳ b.1
参数：h : a ⤳ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `specializes_prod`：specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ 
(x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂
-/
theorem Specializes.fst {a b : X × Y} (h : a ⤳ b) : a.1 ⤳ b.1 := (specializes_prod.1 h).1
/-
**Specializes.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.snd {a b : X × Y} (h : a ⤳ b) : a.2 ⤳ b.2
参数：h : a ⤳ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `specializes_prod`：specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ 
(x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂
-/
theorem Specializes.snd {a b : X × Y} (h : a ⤳ b) : a.2 ⤳ b.2 := (specializes_prod.1 h).2

@[simp]
/-
**specializes_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_pi {f g : forall i, A i} : f ⤳ g ↔ forall i, f i ⤳ g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem specializes_pi {f g : ∀ i, A i} : f ⤳ g ↔ ∀ i, f i ⤳ g i := by
  simp only [Specializes, nhds_pi, pi_le_pi]
/-
**not_specializes_iff_exists_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_specializes_iff_exists_open : ¬x ⤳ y ↔ exists S : Set X, IsOpen S ∧ y 
in S ∧ x ∉ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `specializes_iff_forall_open`：specializes_iff_forall_open : x ⤳ y ↔ foral
l s : Set X, IsOpen s -> y in s -> x in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_specializes_iff_exists_open : ¬x ⤳ y ↔ ∃ S : Set X, IsOpen S ∧ y ∈ S ∧ x ∉ S := by
  rw [specializes_iff_forall_open]
  push Not
  rfl
/-
**not_specializes_iff_exists_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_specializes_iff_exists_closed : ¬x ⤳ y ↔ exists S : Set X, IsClosed S 
∧ x in S ∧ y ∉ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `specializes_iff_forall_closed`：specializes_iff_forall_closed : x ⤳ y ↔ f
orall s : Set X, IsClosed s -> x in s -> y in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_specializes_iff_exists_closed : ¬x ⤳ y ↔ ∃ S : Set X, IsClosed S ∧ x ∈ S ∧ y ∉ S := by
  rw [specializes_iff_forall_closed]
  push Not
  rfl
/-
**IsOpen.continuous_piecewise_of_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.continuous_piecewise_of_specializes [DecidablePred (· in s)] (hs : 
IsOpen s) (hf : Continuous f) (hg : Continuous g) (hspec : forall x, f x ⤳ g x) 
: Continuous (s.piecewise f g)
参数：· in s；hs : IsOpen s；hf : Continuous f；hg : Continuous g；hspec : forall x, f 
x ⤳ g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `Set.piecewise_preimage`：piecewise_preimage (f g : α -> β) (t) : s.piecew
ise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
· 使用定理 `Set.ite_eq_of_subset_right`：ite_eq_of_subset_right (t : Set α) {s₁ s₂ : 
Set α} (h : s₂ subseteq s₁) : t.ite s₁ s₂ = (s₁ inter t) union s₂
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem IsOpen.continuous_piecewise_of_specializes [DecidablePred (· ∈ s)] (hs : IsOpen s)
    (hf : Continuous f) (hg : Continuous g) (hspec : ∀ x, f x ⤳ g x) :
    Continuous (s.piecewise f g) := by
  have : ∀ U, IsOpen U → g ⁻¹' U ⊆ f ⁻¹' U := fun U hU x hx ↦ (hspec x).mem_open hU hx
  rw [continuous_def]
  intro U hU
  rw [piecewise_preimage, ite_eq_of_subset_right _ (this U hU)]
  exact hU.preimage hf |>.inter hs |>.union (hU.preimage hg)
/-
**IsClosed.continuous_piecewise_of_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.continuous_piecewise_of_specializes [DecidablePred (· in s)] (hs 
: IsClosed s) (hf : Continuous f) (hg : Continuous g) (hspec : forall x, g x ⤳ f
 x) : Continuous (s.piecewise f g)
参数：· in s；hs : IsClosed s；hf : Continuous f；hg : Continuous g；hspec : forall x, 
g x ⤳ f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_compl`：piecewise_compl [forall i, Decidable (i in sᶜ)] : s
ᶜ.piecewise f g = s.piecewise g f
· 使用定理 `IsOpen.continuous_piecewise_of_specializes`：IsOpen.continuous_piecewise_
of_specializes [DecidablePred (· in s)] (hs : IsOpen s) (hf : Continuous f) (hg 
: Continuous g) (hspec : forall …
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem IsClosed.continuous_piecewise_of_specializes [DecidablePred (· ∈ s)] (hs : IsClosed s)
    (hf : Continuous f) (hg : Continuous g) (hspec : ∀ x, g x ⤳ f x) :
    Continuous (s.piecewise f g) := by
  simpa only [piecewise_compl] using hs.isOpen_compl.continuous_piecewise_of_specializes hg hf hspec
/-
**Specializes.clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.clusterPt {f : Filter X} (h : x ⤳ y) (hx : ClusterPt x f) : Cl
usterPt y f
参数：h : x ⤳ y；hx : ClusterPt x f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
-/
theorem Specializes.clusterPt {f : Filter X} (h : x ⤳ y) (hx : ClusterPt x f) :
    ClusterPt y f :=
  Filter.NeBot.mono hx <| inf_le_inf_right _ h
/-
**IsCompact.of_subset_of_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.of_subset_of_specializes {s t : Set X} (hs : IsCompact s) (hts :
 t subseteq s) (h : forall x in s, exists y in t, x ⤳ y) : IsCompact t
参数：hs : IsCompact s；hts : t subseteq s；h : forall x in s, exists y in t, x ⤳ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `Specializes.clusterPt`：Specializes.clusterPt {f : Filter X} (h : x ⤳ y) 
(hx : ClusterPt x f) : ClusterPt y f
-/
theorem IsCompact.of_subset_of_specializes {s t : Set X} (hs : IsCompact s) (hts : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, x ⤳ y) : IsCompact t := by
  intro f _ hf
  obtain ⟨x, hxs, hxf⟩ := hs <| hf.trans <| Filter.monotone_principal hts
  obtain ⟨y, hyt, hxy⟩ := h x hxs
  exact ⟨y, hyt, hxy.clusterPt hxf⟩

attribute [local instance] specializationPreorder

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
/-
**Continuous.specialization_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.specialization_monotone (hf : Continuous f) : Monotone f
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y

--- 原说明 ---
A continuous function is monotone with respect to the specialization preorders o
n the domain and
the codomain.
-/
theorem Continuous.specialization_monotone (hf : Continuous f) : Monotone f :=
  fun _ _ h => h.map hf
/-
**closure_singleton_eq_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_singleton_eq_Iic (x : X) : closure {x} = Iic x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
-/
lemma closure_singleton_eq_Iic (x : X) : closure {x} = Iic x :=
  Set.ext fun _ ↦ specializes_iff_mem_closure.symm

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `x ⤳ y`. -/
/-
**StableUnderSpecialization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StableUnderSpecialization (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `x ⤳ y`.
-/
def StableUnderSpecialization (s : Set X) : Prop :=
  ∀ ⦃x y⦄, x ⤳ y → x ∈ s → y ∈ s

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `y ⤳ x`. -/
/-
**StableUnderGeneralization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StableUnderGeneralization (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `y ⤳ x`.
-/
def StableUnderGeneralization (s : Set X) : Prop :=
  ∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {s : Set X} : StableUnderSpecialization s ↔ IsLowerSet s := Iff.rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {s : Set X} : StableUnderGeneralization s ↔ IsUpperSet s := Iff.rfl
/-
**IsClosed.stableUnderSpecialization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.stableUnderSpecialization {s : Set X} (hs : IsClosed s) : StableU
nderSpecialization s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_closed`：Specializes.mem_closed (h : x ⤳ y) (hs : IsClose
d s) (hx : x in s) : y in s
-/
lemma IsClosed.stableUnderSpecialization {s : Set X} (hs : IsClosed s) :
    StableUnderSpecialization s :=
  fun _ _ e ↦ e.mem_closed hs
/-
**IsOpen.stableUnderGeneralization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.stableUnderGeneralization {s : Set X} (hs : IsOpen s) : StableUnder
Generalization s
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
-/
lemma IsOpen.stableUnderGeneralization {s : Set X} (hs : IsOpen s) :
    StableUnderGeneralization s :=
  fun _ _ e ↦ e.mem_open hs

@[simp]
/-
**stableUnderSpecialization_compl_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_compl_iff {s : Set X} : StableUnderSpecializatio
n sᶜ ↔ StableUnderGeneralization s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 sᶜ ↔ IsUpperSet s
-/
lemma stableUnderSpecialization_compl_iff {s : Set X} :
    StableUnderSpecialization sᶜ ↔ StableUnderGeneralization s :=
  isLowerSet_compl

@[simp]
/-
**stableUnderGeneralization_compl_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_compl_iff {s : Set X} : StableUnderGeneralizatio
n sᶜ ↔ StableUnderSpecialization s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_compl`：isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s
-/
lemma stableUnderGeneralization_compl_iff {s : Set X} :
    StableUnderGeneralization sᶜ ↔ StableUnderSpecialization s :=
  isUpperSet_compl

alias ⟨_, StableUnderGeneralization.compl⟩ := stableUnderSpecialization_compl_iff
alias ⟨_, StableUnderSpecialization.compl⟩ := stableUnderGeneralization_compl_iff
/-
**stableUnderSpecialization_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_univ : StableUnderSpecialization (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
-/
lemma stableUnderSpecialization_univ : StableUnderSpecialization (univ : Set X) := isLowerSet_univ
/-
**stableUnderSpecialization_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_empty : StableUnderSpecialization (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_empty`：∀ {α : Type u_1} [inst : LE α], IsLowerSet ∅
-/
lemma stableUnderSpecialization_empty : StableUnderSpecialization (∅ : Set X) := isLowerSet_empty
/-
**stableUnderGeneralization_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_univ : StableUnderGeneralization (univ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_univ`：isUpperSet_univ : IsUpperSet (univ : Set α)
-/
lemma stableUnderGeneralization_univ : StableUnderGeneralization (univ : Set X) := isUpperSet_univ
/-
**stableUnderGeneralization_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_empty : StableUnderGeneralization (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_empty`：isUpperSet_empty : IsUpperSet (∅ : Set α)
-/
lemma stableUnderGeneralization_empty : StableUnderGeneralization (∅ : Set X) := isUpperSet_empty
/-
**stableUnderSpecialization_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_sUnion (S : Set (Set X)) (H : forall s in S, Sta
bleUnderSpecialization s) : StableUnderSpecialization (⋃₀ S)
参数：S : Set (Set X)；H : forall s in S, StableUnderSpecialization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_sUnion`：∀ {α : Type u_1} [inst : LE α] {S : Set (Set α)}, (∀ 
s ∈ S, IsLowerSet s) → IsLowerSet (⋃₀ S)
-/
lemma stableUnderSpecialization_sUnion (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderSpecialization s) : StableUnderSpecialization (⋃₀ S) :=
  isLowerSet_sUnion H
/-
**stableUnderSpecialization_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_sInter (S : Set (Set X)) (H : forall s in S, Sta
bleUnderSpecialization s) : StableUnderSpecialization (⋂₀ S)
参数：S : Set (Set X)；H : forall s in S, StableUnderSpecialization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_sInter`：∀ {α : Type u_1} [inst : LE α] {S : Set (Set α)}, (∀ 
s ∈ S, IsLowerSet s) → IsLowerSet (⋂₀ S)
-/
lemma stableUnderSpecialization_sInter (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderSpecialization s) : StableUnderSpecialization (⋂₀ S) :=
  isLowerSet_sInter H
/-
**stableUnderGeneralization_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_sUnion (S : Set (Set X)) (H : forall s in S, Sta
bleUnderGeneralization s) : StableUnderGeneralization (⋃₀ S)
参数：S : Set (Set X)；H : forall s in S, StableUnderGeneralization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sUnion`：isUpperSet_sUnion {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋃₀ S)
-/
lemma stableUnderGeneralization_sUnion (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderGeneralization s) : StableUnderGeneralization (⋃₀ S) :=
  isUpperSet_sUnion H
/-
**stableUnderGeneralization_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_sInter (S : Set (Set X)) (H : forall s in S, Sta
bleUnderGeneralization s) : StableUnderGeneralization (⋂₀ S)
参数：S : Set (Set X)；H : forall s in S, StableUnderGeneralization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sInter`：isUpperSet_sInter {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋂₀ S)
-/
lemma stableUnderGeneralization_sInter (S : Set (Set X))
    (H : ∀ s ∈ S, StableUnderGeneralization s) : StableUnderGeneralization (⋂₀ S) :=
  isUpperSet_sInter H
/-
**stableUnderSpecialization_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_iUnion {ι : Sort*} (S : ι -> Set X) (H : forall 
i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋃ i, S i)
参数：S : ι -> Set X；H : forall i, StableUnderSpecialization (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_iUnion`：∀ {α : Type u_1} {ι : Sort u_3} [inst : LE α] {f : ι 
→ Set α}, (∀ (i : ι), IsLowerSet (f i)) → IsLowerSet (⋃ i, f i)
-/
lemma stableUnderSpecialization_iUnion {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋃ i, S i) :=
  isLowerSet_iUnion H
/-
**stableUnderSpecialization_iInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_iInter {ι : Sort*} (S : ι -> Set X) (H : forall 
i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋂ i, S i)
参数：S : ι -> Set X；H : forall i, StableUnderSpecialization (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLowerSet_iInter`：∀ {α : Type u_1} {ι : Sort u_3} [inst : LE α] {f : ι 
→ Set α}, (∀ (i : ι), IsLowerSet (f i)) → IsLowerSet (⋂ i, f i)
-/
lemma stableUnderSpecialization_iInter {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋂ i, S i) :=
  isLowerSet_iInter H
/-
**stableUnderGeneralization_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_iUnion {ι : Sort*} (S : ι -> Set X) (H : forall 
i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋃ i, S i)
参数：S : ι -> Set X；H : forall i, StableUnderGeneralization (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_iUnion`：isUpperSet_iUnion {f : ι -> Set α} (hf : forall i, Is
UpperSet (f i)) : IsUpperSet (⋃ i, f i)
-/
lemma stableUnderGeneralization_iUnion {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋃ i, S i) :=
  isUpperSet_iUnion H
/-
**stableUnderGeneralization_iInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_iInter {ι : Sort*} (S : ι -> Set X) (H : forall 
i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋂ i, S i)
参数：S : ι -> Set X；H : forall i, StableUnderGeneralization (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_iInter`：isUpperSet_iInter {f : ι -> Set α} (hf : forall i, Is
UpperSet (f i)) : IsUpperSet (⋂ i, f i)
-/
lemma stableUnderGeneralization_iInter {ι : Sort*} (S : ι → Set X)
    (H : ∀ i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋂ i, S i) :=
  isUpperSet_iInter H
/-
**Union_closure_singleton_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Union_closure_singleton_eq_iff {s : Set X} : (⋃ x in s, closure {x}) = s ↔
 StableUnderSpecialization s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `closure_singleton_eq_Iic`：closure_singleton_eq_Iic (x : X) : closure {x}
 = Iic x
· 使用定理 `coe_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] (s : Set α), ↑(lo
werClosure s) = ⋃ a ∈ s, Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Union_closure_singleton_eq_iff {s : Set X} :
    (⋃ x ∈ s, closure {x}) = s ↔ StableUnderSpecialization s :=
  show _ ↔ IsLowerSet s by simp only [closure_singleton_eq_Iic, ← lowerClosure_eq, coe_lowerClosure]
/-
**stableUnderSpecialization_iff_Union_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_iff_Union_eq {s : Set X} : StableUnderSpecializa
tion s ↔ (⋃ x in s, closure {x}) = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Union_closure_singleton_eq_iff`：Union_closure_singleton_eq_iff {s : Set 
X} : (⋃ x in s, closure {x}) = s ↔ StableUnderSpecialization s
-/
lemma stableUnderSpecialization_iff_Union_eq {s : Set X} :
    StableUnderSpecialization s ↔ (⋃ x ∈ s, closure {x}) = s :=
  Union_closure_singleton_eq_iff.symm

alias ⟨StableUnderSpecialization.Union_eq, _⟩ := stableUnderSpecialization_iff_Union_eq

/-- A set is stable under specialization iff it is a union of closed sets. -/
/-
**stableUnderSpecialization_iff_exists_sUnion_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderSpecialization_iff_exists_sUnion_eq {s : Set X} : StableUnderSp
ecialization s ↔ exists (S : Set (Set X)), (forall s in S, IsClosed s) ∧ ⋃₀ S = 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StableUnderSpecialization.Union_eq`：∀ {X : Type u_1} [inst : Topological
Space X] {s : Set X}, StableUnderSpecialization s → ⋃ x ∈ s, closure {x} = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `stableUnderSpecialization_sUnion`：stableUnderSpecialization_sUnion (S : 
Set (Set X)) (H : forall s in S, StableUnderSpecialization s) : StableUnderSpeci
alization (⋃₀ S)
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s

--- 原说明 ---
A set is stable under specialization iff it is a union of closed sets.
-/
lemma stableUnderSpecialization_iff_exists_sUnion_eq {s : Set X} :
    StableUnderSpecialization s ↔ ∃ (S : Set (Set X)), (∀ s ∈ S, IsClosed s) ∧ ⋃₀ S = s := by
  refine ⟨fun H ↦ ⟨(fun x : X ↦ closure {x}) '' s, ?_, ?_⟩, fun ⟨S, hS, e⟩ ↦ e ▸
    stableUnderSpecialization_sUnion S (fun x hx ↦ (hS x hx).stableUnderSpecialization)⟩
  · rintro _ ⟨_, _, rfl⟩; exact isClosed_closure
  · conv_rhs => rw [← H.Union_eq]
    simp

/-- A set is stable under generalization iff it is an intersection of open sets. -/
/-
**stableUnderGeneralization_iff_exists_sInter_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：stableUnderGeneralization_iff_exists_sInter_eq {s : Set X} : StableUnderGe
neralization s ↔ exists (S : Set (Set X)), (forall s in S, IsOpen s) ∧ ⋂₀ S = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `stableUnderSpecialization_compl_iff`：stableUnderSpecialization_compl_iff
 {s : Set X} : StableUnderSpecialization sᶜ ↔ StableUnderGeneralization s
· 使用引理 `stableUnderSpecialization_iff_exists_sUnion_eq`：stableUnderSpecializatio
n_iff_exists_sUnion_eq {s : Set X} : StableUnderSpecialization s ↔ exists (S : S
et (Set X)), (forall s in S, IsClose…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sUnion_eq_compl_sInter_compl`：sUnion_eq_compl_sInter_compl (S : Set 
(Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ
· 使用引理 `stableUnderGeneralization_sInter`：stableUnderGeneralization_sInter (S : 
Set (Set X)) (H : forall s in S, StableUnderGeneralization s) : StableUnderGener
alization (⋂₀ S)
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s

--- 原说明 ---
A set is stable under generalization iff it is an intersection of open sets.
-/
lemma stableUnderGeneralization_iff_exists_sInter_eq {s : Set X} :
    StableUnderGeneralization s ↔ ∃ (S : Set (Set X)), (∀ s ∈ S, IsOpen s) ∧ ⋂₀ S = s := by
  refine ⟨?_, fun ⟨S, hS, e⟩ ↦ e ▸
    stableUnderGeneralization_sInter S (fun x hx ↦ (hS x hx).stableUnderGeneralization)⟩
  rw [← stableUnderSpecialization_compl_iff, stableUnderSpecialization_iff_exists_sUnion_eq]
  exact fun ⟨S, h₁, h₂⟩ ↦ ⟨(·ᶜ) '' S, fun s ⟨t, ht, e⟩ ↦ e ▸ (h₁ t ht).isOpen_compl,
    compl_injective ((sUnion_eq_compl_sInter_compl S).symm.trans h₂)⟩
/-
**StableUnderSpecialization.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StableUnderSpecialization.preimage {s : Set Y} (hs : StableUnderSpecializa
tion s) (hf : Continuous f) : StableUnderSpecialization (f ⁻¹' s)
参数：hs : StableUnderSpecialization s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.preimage`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] {s : Set α},   IsLowerSet s → ∀ {f : β → α}, Monotone f →
 IsLowerS…
· 使用定理 `Continuous.specialization_monotone`：Continuous.specialization_monotone (
hf : Continuous f) : Monotone f
-/
lemma StableUnderSpecialization.preimage {s : Set Y}
    (hs : StableUnderSpecialization s) (hf : Continuous f) :
    StableUnderSpecialization (f ⁻¹' s) :=
  IsLowerSet.preimage hs hf.specialization_monotone
/-
**StableUnderGeneralization.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StableUnderGeneralization.preimage {s : Set Y} (hs : StableUnderGeneraliza
tion s) (hf : Continuous f) : StableUnderGeneralization (f ⁻¹' s)
参数：hs : StableUnderGeneralization s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.preimage`：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α
} (hf : Monotone f) : IsUpperSet (f ⁻¹' s : Set β)
· 使用定理 `Continuous.specialization_monotone`：Continuous.specialization_monotone (
hf : Continuous f) : Monotone f
-/
lemma StableUnderGeneralization.preimage {s : Set Y}
    (hs : StableUnderGeneralization s) (hf : Continuous f) :
    StableUnderGeneralization (f ⁻¹' s) :=
  IsUpperSet.preimage hs hf.specialization_monotone

/-- A map `f` between topological spaces is specializing if specializations lifts along `f`,
i.e. for each `f x' ⤳ y` there is some `x` with `x' ⤳ x` whose image is `y`. -/
/-
**SpecializingMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SpecializingMap (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` between topological spaces is specializing if specializations lifts al
ong `f`,
i.e. for each `f x' ⤳ y` there is some `x` with `x' ⤳ x` whose image is `y`.
-/
def SpecializingMap (f : X → Y) : Prop :=
  Relation.Fibration (flip (· ⤳ ·)) (flip (· ⤳ ·)) f

/-- A map `f` between topological spaces is generalizing if generalizations lifts along `f`,
i.e. for each `y ⤳ f x'` there is some `x ⤳ x'` whose image is `y`. -/
/-
**GeneralizingMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GeneralizingMap (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` between topological spaces is generalizing if generalizations lifts al
ong `f`,
i.e. for each `y ⤳ f x'` there is some `x ⤳ x'` whose image is `y`.
-/
def GeneralizingMap (f : X → Y) : Prop :=
  Relation.Fibration (· ⤳ ·) (· ⤳ ·) f
/-
**specializingMap_iff_closure_singleton_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：specializingMap_iff_closure_singleton_subset : SpecializingMap f ↔ forall 
x, closure {f x} subseteq f '' closure {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma specializingMap_iff_closure_singleton_subset :
    SpecializingMap f ↔ ∀ x, closure {f x} ⊆ f '' closure {x} := by
  simp only [SpecializingMap, Relation.Fibration, flip, specializes_iff_mem_closure]; rfl

alias ⟨SpecializingMap.closure_singleton_subset, _⟩ := specializingMap_iff_closure_singleton_subset
/-
**SpecializingMap.stableUnderSpecialization_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpecializingMap.stableUnderSpecialization_image (hf : SpecializingMap f) {
s : Set X} (hs : StableUnderSpecialization s) : StableUnderSpecialization (f '' 
s)
参数：hf : SpecializingMap f；hs : StableUnderSpecialization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.image_fibration`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
[inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≤ x2) (fun 
x1 x2 => x1 ≤ x2…
-/
lemma SpecializingMap.stableUnderSpecialization_image (hf : SpecializingMap f)
    {s : Set X} (hs : StableUnderSpecialization s) : StableUnderSpecialization (f '' s) :=
  IsLowerSet.image_fibration hf hs

alias StableUnderSpecialization.image := SpecializingMap.stableUnderSpecialization_image
/-
**specializingMap_iff_stableUnderSpecialization_image_singleton** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：specializingMap_iff_stableUnderSpecialization_image_singleton : Specializi
ngMap f ↔ forall x, StableUnderSpecialization (f '' closure {x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `closure_singleton_eq_Iic`：closure_singleton_eq_Iic (x : X) : closure {x}
 = Iic x
· 使用引理 `Relation.fibration_iff_isLowerSet_image_Iic`：fibration_iff_isLowerSet_im
age_Iic [Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall x, IsLowerS
et (f '' Iic x)
-/
lemma specializingMap_iff_stableUnderSpecialization_image_singleton :
    SpecializingMap f ↔ ∀ x, StableUnderSpecialization (f '' closure {x}) := by
  simpa only [closure_singleton_eq_Iic] using! Relation.fibration_iff_isLowerSet_image_Iic
/-
**specializingMap_iff_stableUnderSpecialization_image** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：specializingMap_iff_stableUnderSpecialization_image : SpecializingMap f ↔ 
forall s, StableUnderSpecialization s -> StableUnderSpecialization (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.fibration_iff_isLowerSet_image`：fibration_iff_isLowerSet_image 
[Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall s, IsLowerSet s -> 
IsLowerSet (f '' s)
-/
lemma specializingMap_iff_stableUnderSpecialization_image :
    SpecializingMap f ↔ ∀ s, StableUnderSpecialization s → StableUnderSpecialization (f '' s) :=
  Relation.fibration_iff_isLowerSet_image
/-
**specializingMap_iff_closure_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：specializingMap_iff_closure_singleton (hf : Continuous f) : SpecializingMa
p f ↔ forall x, f '' closure {x} = closure {f x}
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `closure_singleton_eq_Iic`：closure_singleton_eq_Iic (x : X) : closure {x}
 = Iic x
· 使用引理 `Relation.fibration_iff_image_Iic`：fibration_iff_image_Iic [Preorder α] [
Preorder β] (hf : Monotone f) : Fibration (· <= ·) (· <= ·) f ↔ forall x, f '' I
ic x = Iic (f x)
· 使用定理 `Continuous.specialization_monotone`：Continuous.specialization_monotone (
hf : Continuous f) : Monotone f
-/
lemma specializingMap_iff_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ ∀ x, f '' closure {x} = closure {f x} := by
  simpa only [closure_singleton_eq_Iic] using!
    Relation.fibration_iff_image_Iic hf.specialization_monotone
/-
**specializingMap_iff_isClosed_image_closure_singleton** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：specializingMap_iff_isClosed_image_closure_singleton (hf : Continuous f) :
 SpecializingMap f ↔ forall x, IsClosed (f '' closure {x})
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `specializingMap_iff_closure_singleton`：specializingMap_iff_closure_singl
eton (hf : Continuous f) : SpecializingMap f ↔ forall x, f '' closure {x} = clos
ure {f x}
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `specializingMap_iff_stableUnderSpecialization_image_singleton`：specializ
ingMap_iff_stableUnderSpecialization_image_singleton : SpecializingMap f ↔ foral
l x, StableUnderSpecialization (f '' closure {x})
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
-/
lemma specializingMap_iff_isClosed_image_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ ∀ x, IsClosed (f '' closure {x}) := by
  refine ⟨fun h x ↦ ?_, fun h ↦ specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    (fun x ↦ (h x).stableUnderSpecialization)⟩
  rw [(specializingMap_iff_closure_singleton hf).mp h x]
  exact isClosed_closure
/-
**SpecializingMap.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpecializingMap.comp {f : X -> Y} {g : Y -> Z} (hf : SpecializingMap f) (h
g : SpecializingMap g) : SpecializingMap (g ∘ f)
参数：hf : SpecializingMap f；hg : SpecializingMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
lemma SpecializingMap.comp {f : X → Y} {g : Y → Z}
    (hf : SpecializingMap f) (hg : SpecializingMap g) :
    SpecializingMap (g ∘ f) := by
  simp only [specializingMap_iff_stableUnderSpecialization_image, Set.image_comp] at *
  exact fun s h ↦ hg _ (hf _ h)
/-
**IsClosedMap.specializingMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosedMap.specializingMap (hf : IsClosedMap f) : SpecializingMap f
参数：hf : IsClosedMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `specializingMap_iff_stableUnderSpecialization_image_singleton`：specializ
ingMap_iff_stableUnderSpecialization_image_singleton : SpecializingMap f ↔ foral
l x, StableUnderSpecialization (f '' closure {x})
· 使用引理 `IsClosed.stableUnderSpecialization`：IsClosed.stableUnderSpecialization {
s : Set X} (hs : IsClosed s) : StableUnderSpecialization s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
lemma IsClosedMap.specializingMap (hf : IsClosedMap f) : SpecializingMap f :=
  specializingMap_iff_stableUnderSpecialization_image_singleton.mpr <|
    fun _ ↦ (hf _ isClosed_closure).stableUnderSpecialization
/-
**Topology.IsInducing.specializingMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.specializingMap (hf : IsInducing f) (h : StableUnderSp
ecialization (range f)) : SpecializingMap f
参数：hf : IsInducing f；h : StableUnderSpecialization (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
-/
lemma Topology.IsInducing.specializingMap (hf : IsInducing f)
    (h : StableUnderSpecialization (range f)) : SpecializingMap f := by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩
/-
**Topology.IsInducing.generalizingMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.generalizingMap (hf : IsInducing f) (h : StableUnderGe
neralization (range f)) : GeneralizingMap f
参数：hf : IsInducing f；h : StableUnderGeneralization (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
-/
lemma Topology.IsInducing.generalizingMap (hf : IsInducing f)
    (h : StableUnderGeneralization (range f)) : GeneralizingMap f := by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩
/-
**Topology.IsOpenEmbedding.generalizingMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.generalizingMap (hf : IsOpenEmbedding f) : Genera
lizingMap f
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.generalizingMap`：Topology.IsInducing.generalizingMap
 (hf : IsInducing f) (h : StableUnderGeneralization (range f)) : GeneralizingMap
 f
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
lemma Topology.IsOpenEmbedding.generalizingMap (hf : IsOpenEmbedding f) : GeneralizingMap f :=
  hf.isInducing.generalizingMap hf.isOpen_range.stableUnderGeneralization
/-
**SpecializingMap.stableUnderSpecialization_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpecializingMap.stableUnderSpecialization_range (h : SpecializingMap f) : 
StableUnderSpecialization (range f)
参数：h : SpecializingMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StableUnderSpecialization.image`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   SpecializingMa
p f → ∀ {s : Set X}, …
· 使用引理 `stableUnderSpecialization_univ`：stableUnderSpecialization_univ : StableU
nderSpecialization (univ : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma SpecializingMap.stableUnderSpecialization_range (h : SpecializingMap f) :
    StableUnderSpecialization (range f) :=
  @image_univ _ _ f ▸ stableUnderSpecialization_univ.image h
/-
**GeneralizingMap.stableUnderGeneralization_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GeneralizingMap.stableUnderGeneralization_image (hf : GeneralizingMap f) {
s : Set X} (hs : StableUnderGeneralization s) : StableUnderGeneralization (f '' 
s)
参数：hf : GeneralizingMap f；hs : StableUnderGeneralization s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.image_fibration`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
[inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≥ x2) (fun 
x1 x2 => x1 ≥ x2…
-/
lemma GeneralizingMap.stableUnderGeneralization_image (hf : GeneralizingMap f) {s : Set X}
    (hs : StableUnderGeneralization s) : StableUnderGeneralization (f '' s) :=
  IsUpperSet.image_fibration hf hs
/-
**GeneralizingMap_iff_stableUnderGeneralization_image** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：GeneralizingMap_iff_stableUnderGeneralization_image : GeneralizingMap f ↔ 
forall s, StableUnderGeneralization s -> StableUnderGeneralization (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.fibration_iff_isUpperSet_image`：fibration_iff_isUpperSet_image 
[Preorder α] [LE β] : Fibration (· >= ·) (· >= ·) f ↔ forall s, IsUpperSet s -> 
IsUpperSet (f '' s)
-/
lemma GeneralizingMap_iff_stableUnderGeneralization_image :
    GeneralizingMap f ↔ ∀ s, StableUnderGeneralization s → StableUnderGeneralization (f '' s) :=
  Relation.fibration_iff_isUpperSet_image

alias StableUnderGeneralization.image := GeneralizingMap.stableUnderGeneralization_image
/-
**GeneralizingMap.stableUnderGeneralization_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GeneralizingMap.stableUnderGeneralization_range (h : GeneralizingMap f) : 
StableUnderGeneralization (range f)
参数：h : GeneralizingMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StableUnderGeneralization.image`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   GeneralizingMa
p f → ∀ {s : Set X}, …
· 使用引理 `stableUnderGeneralization_univ`：stableUnderGeneralization_univ : StableU
nderGeneralization (univ : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma GeneralizingMap.stableUnderGeneralization_range (h : GeneralizingMap f) :
    StableUnderGeneralization (range f) :=
  @image_univ _ _ f ▸ stableUnderGeneralization_univ.image h
/-
**GeneralizingMap.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GeneralizingMap.comp {f : X -> Y} {g : Y -> Z} (hf : GeneralizingMap f) (h
g : GeneralizingMap g) : GeneralizingMap (g ∘ f)
参数：hf : GeneralizingMap f；hg : GeneralizingMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
lemma GeneralizingMap.comp {f : X → Y} {g : Y → Z}
    (hf : GeneralizingMap f) (hg : GeneralizingMap g) :
    GeneralizingMap (g ∘ f) := by
  simp only [GeneralizingMap_iff_stableUnderGeneralization_image, Set.image_comp] at *
  exact fun s h ↦ hg _ (hf _ h)

/-!
### `Inseparable` relation
-/

local infixl:0 " ~ᵢ " => Inseparable

/-
**inseparable_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_def : (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inseparable_def : (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl
/-
**inseparable_iff_specializes_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_specializes_and : (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
-/
theorem inseparable_iff_specializes_and : (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iff
/-
**Inseparable.specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
参数：h : x ~ᵢ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y := h.le
/-
**Inseparable.specializes'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x
参数：h : x ~ᵢ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x := h.ge
/-
**Specializes.antisymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ᵢ y
参数：h₁ : x ⤳ y；h₂ : y ⤳ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ᵢ y :=
  le_antisymm h₁ h₂
/-
**inseparable_iff_forall_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_forall_isOpen : (x ~ᵢ y) ↔ forall s : Set X, IsOpen s -> (
x in s ↔ y in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_iff_forall_isOpen : (x ~ᵢ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]
/-
**not_inseparable_iff_exists_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_inseparable_iff_exists_open : ¬(x ~ᵢ y) ↔ exists s : Set X, IsOpen s ∧
 Xor (x in s) (y in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_inseparable_iff_exists_open :
    ¬(x ~ᵢ y) ↔ ∃ s : Set X, IsOpen s ∧ Xor (x ∈ s) (y ∈ s) := by
  simp [inseparable_iff_forall_isOpen, ← xor_iff_not_iff]
/-
**inseparable_iff_forall_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_forall_isClosed : (x ~ᵢ y) ↔ forall s : Set X, IsClosed s 
-> (x in s ↔ y in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_iff_forall_isClosed : (x ~ᵢ y) ↔ ∀ s : Set X, IsClosed s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]
/-
**inseparable_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_mem_closure : (x ~ᵢ y) ↔ x in closure ({y} : Set X) ∧ y in
 closure ({x} : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `inseparable_iff_specializes_and`：inseparable_iff_specializes_and : (x ~ᵢ
 y) ↔ x ⤳ y ∧ y ⤳ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_iff_mem_closure :
    (x ~ᵢ y) ↔ x ∈ closure ({y} : Set X) ∧ y ∈ closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by simp only [specializes_iff_mem_closure, and_comm]
/-
**inseparable_iff_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_closure_eq : (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y
}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_iff_closure_eq : (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y} := by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]
/-
**inseparable_of_nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_of_nhdsWithin_eq (hx : x in s) (hy : y in s) (h : 𝓝[s] x = 𝓝[s
] y) : x ~ᵢ y
参数：hx : x in s；hy : y in s；h : 𝓝[s] x = 𝓝[s] y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `specializes_of_nhdsWithin`：specializes_of_nhdsWithin (h₁ : 𝓝[s] x <= 𝓝[s
] y) (h₂ : x in s) : x ⤳ y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem inseparable_of_nhdsWithin_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ᵢ y :=
  (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)
/-
**Topology.IsInducing.inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.inseparable_iff (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (
x ~ᵢ y)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Topology.IsInducing.inseparable_iff (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y) := by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]
/-
**subtype_inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtype_inseparable_iff {p : X -> Prop} (x y : Subtype p) : (x ~ᵢ y) ↔ ((x
 : X) ~ᵢ y)
参数：x y : Subtype p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
theorem subtype_inseparable_iff {p : X → Prop} (x y : Subtype p) : (x ~ᵢ y) ↔ ((x : X) ~ᵢ y) :=
  IsInducing.subtypeVal.inseparable_iff.symm
/-
**inseparable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {x₁ x₂ : X} {y₁ y₂ : Y},   Inseparable (x₁, y₁) (x₂, y₂) ↔ Insep
arable x₁ x₂ ∧ Inseparable y₁ y₂
参数：x₁, y₁；x₂, y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} :
    ((x₁, y₁) ~ᵢ (x₂, y₂)) ↔ (x₁ ~ᵢ x₂) ∧ (y₁ ~ᵢ y₂) := by
  simp only [Inseparable, nhds_prod_eq, Filter.prod_inj]
/-
**Inseparable.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂) :
 (x₁, y₁) ~ᵢ (x₂, y₂)
参数：hx : x₁ ~ᵢ x₂；hy : y₁ ~ᵢ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inseparable_prod`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] {x₁ x₂ : X} {y₁ y₂ : Y},   Inseparable (x₁, 
y₁) (x…
-/
theorem Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂) :
    (x₁, y₁) ~ᵢ (x₂, y₂) :=
  inseparable_prod.2 ⟨hx, hy⟩

@[simp]
/-
**inseparable_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_pi {f g : forall i, A i} : (f ~ᵢ g) ↔ forall i, f i ~ᵢ g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_pi {f g : ∀ i, A i} : (f ~ᵢ g) ↔ ∀ i, f i ~ᵢ g i := by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]

namespace Inseparable

@[refl]
/-
**Inseparable.refl** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：refl (x : X) : x ~ᵢ x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (x : X) : x ~ᵢ x :=
  Eq.refl (𝓝 x)
/-
**Inseparable.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：rfl : x ~ᵢ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.refl`：refl (x : X) : x ~ᵢ x
-/
theorem rfl : x ~ᵢ x :=
  refl x
/-
**Inseparable.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：of_eq (e : x = y) : Inseparable x y
参数：e : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.refl`：refl (x : X) : x ~ᵢ x
-/
theorem of_eq (e : x = y) : Inseparable x y :=
  e ▸ refl x

@[symm]
nonrec theorem symm (h : x ~ᵢ y) : y ~ᵢ x := h.symm

@[trans]
nonrec theorem trans (h₁ : x ~ᵢ y) (h₂ : y ~ᵢ z) : x ~ᵢ z := h₁.trans h₂
/-
**Inseparable.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：nhds_eq (h : x ~ᵢ y) : 𝓝 x = 𝓝 y
参数：h : x ~ᵢ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_eq (h : x ~ᵢ y) : 𝓝 x = 𝓝 y := h
/-
**Inseparable.mem_open_iff** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x in s ↔ y in s
参数：h : x ~ᵢ y；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inseparable_iff_forall_isOpen`：inseparable_iff_forall_isOpen : (x ~ᵢ y) 
↔ forall s : Set X, IsOpen s -> (x in s ↔ y in s)
-/
theorem mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_isOpen.1 h s hs
/-
**Inseparable.mem_closed_iff** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s) : x in s ↔ y in s
参数：h : x ~ᵢ y；hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inseparable_iff_forall_isClosed`：inseparable_iff_forall_isClosed : (x ~ᵢ
 y) ↔ forall s : Set X, IsClosed s -> (x in s ↔ y in s)
-/
theorem mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_isClosed.1 h s hs
/-
**Inseparable.map_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：map_of_continuousWithinAt {s t : Set X} (h : x ~ᵢ y) (hfx : ContinuousWith
inAt f s x) (hfy : ContinuousWithinAt f t y) (hx : x in t) (hy : y in s) : f x ~
ᵢ f y
参数：h : x ~ᵢ y；hfx : ContinuousWithinAt f s x；hfy : ContinuousWithinAt f t y；hx :
 x in t；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `Specializes.map_of_continuousWithinAt`：Specializes.map_of_continuousWith
inAt {s : Set X} (h : x ⤳ y) (hf : ContinuousWithinAt f s y) (hx : x in s) : f x
 ⤳ f y
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.specializes'`：Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x
-/
theorem map_of_continuousWithinAt {s t : Set X} (h : x ~ᵢ y)
    (hfx : ContinuousWithinAt f s x) (hfy : ContinuousWithinAt f t y)
    (hx : x ∈ t) (hy : y ∈ s) : f x ~ᵢ f y :=
  (h.specializes.map_of_continuousWithinAt hfy hx).antisymm
    (h.specializes'.map_of_continuousWithinAt hfx hy)
/-
**Inseparable.map_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：map_of_continuousOn {s : Set X} (h : x ~ᵢ y) (hf : ContinuousOn f s) (hx :
 x in s) (hy : y in s) : f x ~ᵢ f y
参数：h : x ~ᵢ y；hf : ContinuousOn f s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map_of_continuousWithinAt`：map_of_continuousWithinAt {s t : 
Set X} (h : x ~ᵢ y) (hfx : ContinuousWithinAt f s x) (hfy : ContinuousWithinAt f
 t y) (hx : x in t) (hy : y…
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
-/
theorem map_of_continuousOn {s : Set X} (h : x ~ᵢ y)
    (hf : ContinuousOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ~ᵢ f y :=
  h.map_of_continuousWithinAt (hf.continuousWithinAt hx) (hf.continuousWithinAt hy) hx hy
/-
**Inseparable.map_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：map_of_continuousAt (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousA
t f y) : f x ~ᵢ f y
参数：h : x ~ᵢ y；hx : ContinuousAt f x；hy : ContinuousAt f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map_of_continuousWithinAt`：map_of_continuousWithinAt {s t : 
Set X} (h : x ~ᵢ y) (hfx : ContinuousWithinAt f s x) (hfy : ContinuousWithinAt f
 t y) (hx : x in t) (hy : y…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem map_of_continuousAt (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) :
    f x ~ᵢ f y :=
  h.map_of_continuousWithinAt hx.continuousWithinAt hy.continuousWithinAt (mem_univ x) (mem_univ y)
/-
**Inseparable.map** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
参数：h : x ~ᵢ y；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map_of_continuousAt`：map_of_continuousAt (h : x ~ᵢ y) (hx : 
ContinuousAt f x) (hy : ContinuousAt f y) : f x ~ᵢ f y
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y :=
  h.map_of_continuousAt hf.continuousAt hf.continuousAt

end Inseparable

/-
**IsClosed.not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.not_inseparable (hs : IsClosed s) (hx : x in s) (hy : y ∉ s) : ¬(
x ~ᵢ y)
参数：hs : IsClosed s；hx : x in s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_closed_iff`：mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s
) : x in s ↔ y in s
-/
theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx
/-
**IsOpen.not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.not_inseparable (hs : IsOpen s) (hx : x in s) (hy : y ∉ s) : ¬(x ~ᵢ
 y)
参数：hs : IsOpen s；hx : x in s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
-/
theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `Inseparable` relation.
-/

variable (X) in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (SeparationQuotient X) :=
  inferInstanceAs <| TopologicalSpace (Quotient _)

variable {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
/-
**SeparationQuotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：mk : X -> SeparationQuotient X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The natural map from a topological space to its separation quotient.
-/
def mk : X → SeparationQuotient X := Quotient.mk''
/-
**SeparationQuotient.isQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：isQuotientMap_mk : IsQuotientMap (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_mk : IsQuotientMap (mk : X → SeparationQuotient X) :=
  isQuotientMap_quot_mk

@[fun_prop, continuity]
/-
**SeparationQuotient.continuous_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：continuous_mk : Continuous (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
theorem continuous_mk : Continuous (mk : X → SeparationQuotient X) :=
  continuous_quot_mk

@[simp]
/-
**SeparationQuotient.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y) :=
  Quotient.eq''
/-
**SeparationQuotient.** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {P : SeparationQuotient X → Prop} : (∀ x, P x) ↔ ∀ x, P (.mk x) :=
  Quotient.forall
/-
**SeparationQuotient.** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {P : SeparationQuotient X → Prop} : (∃ x, P x) ↔ ∃ x, P (.mk x) :=
  Quotient.exists
/-
**SeparationQuotient.surjective_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：surjective_mk : Surjective (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem surjective_mk : Surjective (mk : X → SeparationQuotient X) :=
  Quot.mk_surjective

@[simp]
/-
**SeparationQuotient.range_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：range_mk : range (mk : X -> SeparationQuotient X) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
-/
theorem range_mk : range (mk : X → SeparationQuotient X) = univ :=
  surjective_mk.range_eq
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.subsingleton

@[simp]
/-
**SeparationQuotient.inseparableSetoid_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sep
arationQuotient`。
形式化陈述：inseparableSetoid_eq_top_iff [TopologicalSpace α] : inseparableSetoid α = 
⊤ ↔ IndiscreteTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Setoid.eq_top_iff`：eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ fora
ll x y : α, s x y
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `TopologicalSpace.indiscrete_iff_forall_inseparable`：TopologicalSpace.ind
iscrete_iff_forall_inseparable {t : TopologicalSpace α} : IndiscreteTopology α ↔
 (forall x y : α, Inseparable x y) where…
-/
theorem inseparableSetoid_eq_top_iff [TopologicalSpace α] :
    inseparableSetoid α = ⊤ ↔ IndiscreteTopology α :=
  Setoid.eq_top_iff.trans TopologicalSpace.indiscrete_iff_forall_inseparable.symm
/-
**SeparationQuotient.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：subsingleton_iff [TopologicalSpace α] : Subsingleton (SeparationQuotient α
) ↔ IndiscreteTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.subsingleton_iff`：Quotient.subsingleton_iff {s : Setoid α} : Su
bsingleton (Quotient s) ↔ s = ⊤
· 使用定理 `SeparationQuotient.inseparableSetoid_eq_top_iff`：inseparableSetoid_eq_to
p_iff [TopologicalSpace α] : inseparableSetoid α = ⊤ ↔ IndiscreteTopology α
-/
theorem subsingleton_iff [TopologicalSpace α] :
    Subsingleton (SeparationQuotient α) ↔ IndiscreteTopology α :=
  Quotient.subsingleton_iff.trans inseparableSetoid_eq_top_iff
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [IndiscreteTopology α] : Subsingleton (SeparationQuotient α) :=
  subsingleton_iff.2 ‹_›
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [IndiscreteTopology α] {p : α → Prop} :
    IndiscreteTopology (Subtype p) := by
  simp [TopologicalSpace.indiscrete_iff_forall_inseparable, subtype_inseparable_iff]
/-
**SeparationQuotient.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotien
t`。
形式化陈述：nontrivial_iff [TopologicalSpace α] : Nontrivial (SeparationQuotient α) ↔ 
NontrivialTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SeparationQuotient.subsingleton_iff`：subsingleton_iff [TopologicalSpace 
α] : Subsingleton (SeparationQuotient α) ↔ IndiscreteTopology α
-/
theorem nontrivial_iff [TopologicalSpace α] :
    Nontrivial (SeparationQuotient α) ↔ NontrivialTopology α := by
  simpa [not_subsingleton_iff_nontrivial] using subsingleton_iff.not
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [NontrivialTopology α] : Nontrivial (SeparationQuotient α) :=
  nontrivial_iff.2 ‹_›
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One X] : One (SeparationQuotient X) := ⟨mk 1⟩
/-
**SeparationQuotient.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : One X], SeparationQ
uotient.mk 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem mk_one [One X] : mk (1 : X) = 1 := rfl
/-
**SeparationQuotient.preimage_image_mk_open** 是 Mathlib 中的一个定理，位于命名空间 `Separatio
nQuotient`。
形式化陈述：preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' mk '' s = s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' mk '' s = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys
/-
**SeparationQuotient.isOpenMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`
。
形式化陈述：isOpenMap_mk : IsOpenMap (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `SeparationQuotient.isQuotientMap_mk`：isQuotientMap_mk : IsQuotientMap (m
k : X -> SeparationQuotient X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.preimage_image_mk_open`：preimage_image_mk_open (hs : 
IsOpen s) : mk ⁻¹' mk '' s = s
-/
theorem isOpenMap_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  isQuotientMap_mk.isOpen_preimage.1 <| by rwa [preimage_image_mk_open hs]
/-
**SeparationQuotient.isOpenQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：isOpenQuotientMap_mk : IsOpenQuotientMap (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.isOpenMap_mk`：isOpenMap_mk : IsOpenMap (mk : X -> Sep
arationQuotient X)
-/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : X → SeparationQuotient X) :=
  ⟨surjective_mk, continuous_mk, isOpenMap_mk⟩
/-
**SeparationQuotient.preimage_image_mk_closed** 是 Mathlib 中的一个定理，位于命名空间 `Separat
ionQuotient`。
形式化陈述：preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' mk '' s = s
参数：hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_closed_iff`：mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s
) : x in s ↔ y in s
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' mk '' s = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys
/-
**SeparationQuotient.isInducing_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：isInducing_mk : IsInducing (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.isOpenMap_mk`：isOpenMap_mk : IsOpenMap (mk : X -> Sep
arationQuotient X)
· 使用定理 `SeparationQuotient.preimage_image_mk_open`：preimage_image_mk_open (hs : 
IsOpen s) : mk ⁻¹' mk '' s = s
-/
theorem isInducing_mk : IsInducing (mk : X → SeparationQuotient X) :=
  ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩
/-
**SeparationQuotient.isClosedMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotien
t`。
形式化陈述：isClosedMap_mk : IsClosedMap (mk : X -> SeparationQuotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.isClosedMap`：Topology.IsInducing.isClosedMap (hf : I
sInducing f) (h : IsClosed (range f)) : IsClosedMap f
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.range_mk`：range_mk : range (mk : X -> SeparationQuoti
ent X) = univ
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
theorem isClosedMap_mk : IsClosedMap (mk : X → SeparationQuotient X) :=
  isInducing_mk.isClosedMap <| by rw [range_mk]; exact isClosed_univ

@[simp]
/-
**SeparationQuotient.comap_mk_nhds_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
-/
theorem comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
  (isInducing_mk.nhds_eq_comap _).symm

@[simp]
/-
**SeparationQuotient.comap_mk_nhdsSet_image** 是 Mathlib 中的一个定理，位于命名空间 `Separatio
nQuotient`。
形式化陈述：comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhdsSet_eq_comap`：nhdsSet_eq_comap (hf : IsInducing 
f) (s : Set X) : 𝓝ˢ s = comap f (𝓝ˢ (f '' s))
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
-/
theorem comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
  (isInducing_mk.nhdsSet_eq_comap _).symm

/-- Push-forward of the neighborhood of a point along the projection to the separation quotient
is the neighborhood of its equivalence class. -/
/-
**SeparationQuotient.map_mk_nhds** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.comap_mk_nhds_mk`：comap_mk_nhds_mk : comap mk (𝓝 (mk 
x)) = 𝓝 x
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)

--- 原说明 ---
Push-forward of the neighborhood of a point along the projection to the separati
on quotient
is the neighborhood of its equivalence class.
-/
theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [← comap_mk_nhds_mk, map_comap_of_surjective surjective_mk]
/-
**SeparationQuotient.map_mk_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotien
t`。
形式化陈述：map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.comap_mk_nhdsSet_image`：comap_mk_nhdsSet_image : coma
p mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
-/
theorem map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) := by
  rw [← comap_mk_nhdsSet_image, map_comap_of_surjective surjective_mk]
/-
**SeparationQuotient.comap_mk_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `SeparationQuotient.comap_mk_nhdsSet_image`：comap_mk_nhdsSet_image : coma
p mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s
-/
theorem comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) := by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhdsSet_image]
/-
**SeparationQuotient.preimage_mk_closure** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQu
otient`。
形式化陈述：preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `SeparationQuotient.isOpenMap_mk`：isOpenMap_mk : IsOpenMap (mk : X -> Sep
arationQuotient X)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
-/
theorem preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t
/-
**SeparationQuotient.preimage_mk_interior** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `SeparationQuotient.isOpenMap_mk`：isOpenMap_mk : IsOpenMap (mk : X -> Sep
arationQuotient X)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
-/
theorem preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t
/-
**SeparationQuotient.preimage_mk_frontier** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `SeparationQuotient.isOpenMap_mk`：isOpenMap_mk : IsOpenMap (mk : X -> Sep
arationQuotient X)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
-/
theorem preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t
/-
**SeparationQuotient.image_mk_closure** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：image_mk_closure : mk '' closure s = closure (mk '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `IsClosedMap.closure_image_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → ∀ (s : Set X), clos…
· 使用定理 `SeparationQuotient.isClosedMap_mk`：isClosedMap_mk : IsClosedMap (mk : X 
-> SeparationQuotient X)
-/
theorem image_mk_closure : mk '' closure s = closure (mk '' s) :=
  (image_closure_subset_closure_image continuous_mk).antisymm <|
    isClosedMap_mk.closure_image_subset _
/-
**SeparationQuotient.map_prod_map_mk_nhds** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：map_prod_map_mk_nhds (x : X) (y : Y) : map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝
 (mk x, mk y)
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `SeparationQuotient.map_mk_nhds`：map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x)
-/
theorem map_prod_map_mk_nhds (x : X) (y : Y) :
    map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) := by
  rw [nhds_prod_eq, ← prod_map_map_eq', map_mk_nhds, map_mk_nhds, nhds_prod_eq]
/-
**SeparationQuotient.map_mk_nhdsWithin_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Separ
ationQuotient`。
形式化陈述：map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) : map 
mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x
参数：s : Set (SeparationQuotient X)；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `SeparationQuotient.map_mk_nhds`：map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x)
-/
theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin, ← comap_principal, Filter.push_pull, nhdsWithin, map_mk_nhds]

/-- The map `(x, y) ↦ (mk x, mk y)` is a quotient map. -/
/-
**SeparationQuotient.isQuotientMap_prodMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Separat
ionQuotient`。
形式化陈述：isQuotientMap_prodMap_mk : IsQuotientMap (Prod.map mk mk : X × Y -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `SeparationQuotient.isOpenQuotientMap_mk`：isOpenQuotientMap_mk : IsOpenQu
otientMap (mk : X -> SeparationQuotient X)

--- 原说明 ---
The map `(x, y) ↦ (mk x, mk y)` is a quotient map.
-/
theorem isQuotientMap_prodMap_mk : IsQuotientMap (Prod.map mk mk : X × Y → _) :=
  (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).isQuotientMap

/-- Lift a map `f : X → α` such that `Inseparable x y → f x = f y` to a map
`SeparationQuotient X → α`. -/
/-
**SeparationQuotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：lift (f : X -> α) (hf : forall x y, (x ~ᵢ y) -> f x = f y) : SeparationQuo
tient X -> α
参数：f : X -> α；hf : forall x y, (x ~ᵢ y) -> f x = f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a map `f : X → α` such that `Inseparable x y → f x = f y` to a map
`SeparationQuotient X → α`.
-/
def lift (f : X → α) (hf : ∀ x y, (x ~ᵢ y) → f x = f y) : SeparationQuotient X → α := fun x =>
  Quotient.liftOn' x f hf

@[simp]
/-
**SeparationQuotient.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：lift_mk {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y) (x : X) : li
ft f hf (mk x) = f x
参数：hf : forall x y, (x ~ᵢ y) -> f x = f y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk {f : X → α} (hf : ∀ x y, (x ~ᵢ y) → f x = f y) (x : X) : lift f hf (mk x) = f x :=
  rfl

@[simp]
/-
**SeparationQuotient.lift_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`
。
形式化陈述：lift_comp_mk {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y) : lift 
f hf ∘ mk = f
参数：hf : forall x y, (x ~ᵢ y) -> f x = f y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_mk {f : X → α} (hf : ∀ x y, (x ~ᵢ y) → f x = f y) : lift f hf ∘ mk = f :=
  rfl

@[simp]
/-
**SeparationQuotient.tendsto_lift_nhds_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：tendsto_lift_nhds_mk {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y}
 {l : Filter α} : Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l
参数：x ~ᵢ y。
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
theorem tendsto_lift_nhds_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]
/-
**SeparationQuotient.tendsto_lift_nhdsWithin_mk** 是 Mathlib 中的一个定理，位于命名空间 `Separ
ationQuotient`。
形式化陈述：tendsto_lift_nhdsWithin_mk {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x 
= f y} {s : Set (SeparationQuotient X)} {l : Filter α} : Tendsto (lift f hf) (𝓝[
s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l
参数：x ~ᵢ y；SeparationQuotient X。
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
theorem tendsto_lift_nhdsWithin_mk {f : X → α} {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]
/-
**SeparationQuotient.continuousAt_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuot
ient`。
形式化陈述：continuousAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} : ContinuousAt 
(lift f hf) (mk x) ↔ ContinuousAt f x
参数：x ~ᵢ y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.tendsto_lift_nhds_mk`：tendsto_lift_nhds_mk {f : X -> 
α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {l : Filter α} : Tendsto (lift f hf)
 (𝓝 <| mk x) l ↔ Tendsto f (𝓝…
-/
theorem continuousAt_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk

@[simp]
/-
**SeparationQuotient.continuousWithinAt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Separati
onQuotient`。
形式化陈述：continuousWithinAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set 
(SeparationQuotient X)} : ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWi
thinAt f (mk ⁻¹' s) x
参数：x ~ᵢ y；SeparationQuotient X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.tendsto_lift_nhdsWithin_mk`：tendsto_lift_nhdsWithin_m
k {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (SeparationQuot
ient X)} {l : Filter α} : Tendsto (…
-/
theorem continuousWithinAt_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y}
    {s : Set (SeparationQuotient X)} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhdsWithin_mk

@[simp]
/-
**SeparationQuotient.continuousOn_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuot
ient`。
形式化陈述：continuousOn_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (Separ
ationQuotient X)} : ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s)
参数：x ~ᵢ y；SeparationQuotient X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_lift {hf : ∀ x y, (x ~ᵢ y) → f x = f y} {s : Set (SeparationQuotient X)} :
    ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]
/-
**SeparationQuotient.continuous_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQu
otient`。
形式化陈述：continuous_lift_iff {hf : forall x y, (x ~ᵢ y) -> f x = f y} : Continuous 
(lift f hf) ↔ Continuous f
参数：x ~ᵢ y。
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
theorem continuous_lift_iff {hf : ∀ x y, (x ~ᵢ y) → f x = f y} :
    Continuous (lift f hf) ↔ Continuous f := by
  simp only [← continuousOn_univ, continuousOn_lift, preimage_univ]

alias ⟨_, continuous_lift⟩ := continuous_lift_iff
attribute [fun_prop] continuous_lift

/-- Lift a map `f : X → Y → α` such that `Inseparable a b → Inseparable c d → f a c = f b d` to a
map `SeparationQuotient X → SeparationQuotient Y → α`. -/
/-
**SeparationQuotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：lift (f : X -> α) (hf : forall x y, (x ~ᵢ y) -> f x = f y) : SeparationQuo
tient X -> α
参数：f : X -> α；hf : forall x y, (x ~ᵢ y) -> f x = f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a map `f : X → Y → α` such that `Inseparable a b → Inseparable c d → f a c 
= f b d` to a
map `SeparationQuotient X → SeparationQuotient Y → α`.
-/
def lift₂ (f : X → Y → α) (hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d) :
    SeparationQuotient X → SeparationQuotient Y → α := fun x y => Quotient.liftOn₂' x y f hf

@[simp]
/-
**SeparationQuotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：lift (f : X -> α) (hf : forall x y, (x ~ᵢ y) -> f x = f y) : SeparationQuo
tient X -> α
参数：f : X -> α；hf : forall x y, (x ~ᵢ y) -> f x = f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift₂_mk {f : X → Y → α} (hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d) (x : X)
    (y : Y) : lift₂ f hf (mk x) (mk y) = f x y :=
  rfl

@[simp]
/-
**SeparationQuotient.tendsto_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_lift₂_nhds {f : X → Y → α} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {x : X} {y : Y} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝 (mk x, mk y)) l ↔ Tendsto (uncurry f) (𝓝 (x, y)) l := by
  rw [← map_prod_map_mk_nhds, tendsto_map'_iff]
  rfl
/-
**SeparationQuotient.tendsto_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem tendsto_lift₂_nhdsWithin {f : X → Y → α}
    {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d} {x : X} {y : Y}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝[s] (mk x, mk y)) l ↔
      Tendsto (uncurry f) (𝓝[Prod.map mk mk ⁻¹' s] (x, y)) l := by
  rw [nhdsWithin, ← map_prod_map_mk_nhds, ← Filter.push_pull, comap_principal]
  rfl

@[simp]
/-
**SeparationQuotient.continuousAt_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuot
ient`。
形式化陈述：continuousAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} : ContinuousAt 
(lift f hf) (mk x) ↔ ContinuousAt f x
参数：x ~ᵢ y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.tendsto_lift_nhds_mk`：tendsto_lift_nhds_mk {f : X -> 
α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {l : Filter α} : Tendsto (lift f hf)
 (𝓝 <| mk x) l ↔ Tendsto f (𝓝…
-/
theorem continuousAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {x : X} {y : Y} :
    ContinuousAt (uncurry <| lift₂ f hf) (mk x, mk y) ↔ ContinuousAt (uncurry f) (x, y) :=
  tendsto_lift₂_nhds
/-
**SeparationQuotient.continuousWithinAt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Separati
onQuotient`。
形式化陈述：continuousWithinAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set 
(SeparationQuotient X)} : ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWi
thinAt f (mk ⁻¹' s) x
参数：x ~ᵢ y；SeparationQuotient X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.tendsto_lift_nhdsWithin_mk`：tendsto_lift_nhdsWithin_m
k {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (SeparationQuot
ient X)} {l : Filter α} : Tendsto (…
-/
@[simp] theorem continuousWithinAt_lift₂ {f : X → Y → Z}
    {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {x : X} {y : Y} :
    ContinuousWithinAt (uncurry <| lift₂ f hf) s (mk x, mk y) ↔
      ContinuousWithinAt (uncurry f) (Prod.map mk mk ⁻¹' s) (x, y) :=
  tendsto_lift₂_nhdsWithin

@[simp]
/-
**SeparationQuotient.continuousOn_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuot
ient`。
形式化陈述：continuousOn_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (Separ
ationQuotient X)} : ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s)
参数：x ~ᵢ y；SeparationQuotient X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} :
    ContinuousOn (uncurry <| lift₂ f hf) s ↔ ContinuousOn (uncurry f) (Prod.map mk mk ⁻¹' s) := by
  simp_rw [ContinuousOn, (surjective_mk.prodMap surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]
/-
**SeparationQuotient.continuous_lift** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotie
nt`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y}   {hf : ∀ (x y : X), Inseparable x y → f x = f y}, C
ontinuous f → Continuous (SeparationQuotient.lift f hf)
参数：x y : X；SeparationQuotient.lift f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.continuous_lift_iff`：continuous_lift_iff {hf : forall
 x y, (x ~ᵢ y) -> f x = f y} : Continuous (lift f hf) ↔ Continuous f
-/
theorem continuous_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ᵢ c) → (b ~ᵢ d) → f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [← continuousOn_univ, continuousOn_lift₂, preimage_univ]

end SeparationQuotient

/-
**continuous_congr_of_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_congr_of_inseparable (h : forall x, f x ~ᵢ g x) : Continuous f 
↔ Continuous g
参数：h : forall x, f x ~ᵢ g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
· 使用定理 `continuous_congr`：continuous_congr {g : X -> Y} (h : forall x, f x = g x
) : Continuous f ↔ Continuous g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
-/
theorem continuous_congr_of_inseparable (h : ∀ x, f x ~ᵢ g x) :
    Continuous f ↔ Continuous g := by
  simp_rw [SeparationQuotient.isInducing_mk.continuous_iff (Y := Y)]
  exact continuous_congr fun x ↦ SeparationQuotient.mk_eq_mk.mpr (h x)
