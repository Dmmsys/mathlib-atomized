/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Dynamical entourages

Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical entourages. This file collects all general lemmas
about these objects.

## Main definitions

- `dynEntourage`: dynamical entourage associated with a given transformation `T`, entourage `U`
  and time `n`.

## Tags

entropy

## TODO

Add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

@[expose] public section

namespace Dynamics

open Prod Set UniformSpace
open scoped SetRel Topology Uniformity

variable {X : Type*} {T : X → X} {U V : SetRel X X} {m n : ℕ} {x y : X}

/-- The dynamical entourage associated to a transformation `T`, entourage `U` and time `n`
is the entourage where `x` and `y` are close iff `T^[k] x` and `T^[k] y` are `U`-close
for all `k < n`, i.e. iff they are `U`-close up to time `n`. -/
/-
**Dynamics.dynEntourage** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage (T : X -> X) (U : SetRel X X) (n : Nat) : SetRel X X
参数：T : X -> X；U : SetRel X X；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dynamical entourage associated to a transformation `T`, entourage `U` and ti
me `n`
is the entourage where `x` and `y` are close iff `T^[k] x` and `T^[k] y` are `U`
-close
for all `k < n`, i.e. iff they are `U`-close up to time `n`.
-/
def dynEntourage (T : X → X) (U : SetRel X X) (n : ℕ) : SetRel X X :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U
/-
**Dynamics.dynEntourage_eq_inter_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_eq_inter_Ico (T : X -> X) (U : SetRel X X) (n : Nat) : dynEnt
ourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U
参数：T : X -> X；U : SetRel X X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dynEntourage_eq_inter_Ico (T : X → X) (U : SetRel X X) (n : ℕ) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]
/-
**Dynamics.mem_dynEntourage** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：mem_dynEntourage : (x, y) in dynEntourage T U n ↔ forall k < n, (T^[k] x, 
T^[k] y) in U
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_dynEntourage : (x, y) ∈ dynEntourage T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage]
/-
**Dynamics.mem_ball_dynEntourage** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：mem_ball_dynEntourage : y in ball x (dynEntourage T U n) ↔ forall k < n, T
^[k] y in ball (T^[k] x) U
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_ball_dynEntourage :
    y ∈ ball x (dynEntourage T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage, mem_dynEntourage]
/-
**Dynamics.dynEntourage_mem_uniformity** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_mem_uniformity [UniformSpace X] (h : UniformContinuous T) (U_
uni : U in 𝓤 X) (n : Nat) : dynEntourage T U n in 𝓤 X
参数：h : UniformContinuous T；U_uni : U in 𝓤 X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Dynamics.dynEntourage_eq_inter_Ico`：dynEntourage_eq_inter_Ico (T : X -> 
X) (U : SetRel X X) (n : Nat) : dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k
] ⁻¹' U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.biInter_lt_succ`：biInter_lt_succ (u : Nat -> Set α) (n : Nat) : ⋂ k 
< n + 1, u k = (⋂ k < n, u k) inter u n
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_def`：uniformContinuous_def {f : α -> β} : UniformConti
nuous f ↔ forall r in 𝓤 β, { x : α × α | (f x.1, f x.2) in r } in 𝓤 α
· 使用定理 `UniformContinuous.iterate`：UniformContinuous.iterate (T : β -> β) (n : N
at) (h : UniformContinuous T) : UniformContinuous T^[n]
-/
lemma dynEntourage_mem_uniformity [UniformSpace X] (h : UniformContinuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage T U n ∈ 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContinuous.iterate T n h) U U_uni
/-
**Dynamics.ball_dynEntourage_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：ball_dynEntourage_mem_nhds [UniformSpace X] (h : Continuous T) (U_uni : U 
in 𝓤 X) (n : Nat) (x : X) : ball x (dynEntourage T U n) in 𝓝 x
参数：h : Continuous T；U_uni : U in 𝓤 X；n : Nat；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Dynamics.dynEntourage_eq_inter_Ico`：dynEntourage_eq_inter_Ico (T : X -> 
X) (U : SetRel X X) (n : Nat) : dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k
] ⁻¹' U
· 使用定理 `UniformSpace.ball_iInter`：ball_iInter {x : β} {V : ι -> Set (β × β)} : b
all x (⋂ i, V i) = ⋂ i, ball x (V i)
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用引理 `ball_preimage`：ball_preimage {f : α -> β} {U : SetRel β β} {x : α} : Uni
formSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.iterate`：Continuous.iterate {f : X -> X} (h : Continuous f) (
n : Nat) : Continuous f^[n]
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
-/
lemma ball_dynEntourage_mem_nhds [UniformSpace X] (h : Continuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) (x : X) :
    ball x (dynEntourage T U n) ∈ 𝓝 x := by
  rw [dynEntourage_eq_inter_Ico T U n, ball_iInter, Filter.iInter_mem, Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)
/-
**Dynamics.isRefl_dynEntourage** 是 Mathlib 中的一个实例，位于命名空间 `Dynamics`。
形式化陈述：isRefl_dynEntourage [U.IsRefl] : (dynEntourage T U n).IsRefl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
-/
instance isRefl_dynEntourage [U.IsRefl] : (dynEntourage T U n).IsRefl := by
  simp only [dynEntourage, map_iterate]
  infer_instance
/-
**Dynamics.isSymm_dynEntourage** 是 Mathlib 中的一个实例，位于命名空间 `Dynamics`。
形式化陈述：isSymm_dynEntourage [U.IsSymm] : (dynEntourage T U n).IsSymm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
-/
instance isSymm_dynEntourage [U.IsSymm] : (dynEntourage T U n).IsSymm := by
  simp only [dynEntourage, map_iterate]
  infer_instance
/-
**Dynamics.dynEntourage_comp_subset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_comp_subset (T : X -> X) (U V : SetRel X X) (n : Nat) : (dynE
ntourage T U n) ○ (dynEntourage T V n) subseteq dynEntourage T (U ○ V) n
参数：T : X -> X；U V : SetRel X X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `UniformSpace.mem_ball_comp`：mem_ball_comp {V W : Set (β × β)} {x y z} (h
 : y in ball x V) (h' : z in ball y W) : z in ball x (V ○ W)
-/
lemma dynEntourage_comp_subset (T : X → X) (U V : SetRel X X) (n : ℕ) :
    (dynEntourage T U n) ○ (dynEntourage T V n) ⊆ dynEntourage T (U ○ V) n := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [SetRel.comp, mem_iInter, mem_preimage, map_apply, mem_ofPred_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)
/-
**Dynamics._root_.isOpen.dynEntourage** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    (U_open : IsOpen U) (n : ℕ) :
    IsOpen (dynEntourage T U n) := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)
/-
**Dynamics.dynEntourage_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_monotone (T : X -> X) (n : Nat) : Monotone (fun U : SetRel X 
X => dynEntourage T U n)
参数：T : X -> X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma dynEntourage_monotone (T : X → X) (n : ℕ) :
    Monotone (fun U : SetRel X X ↦ dynEntourage T U n) :=
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h
/-
**Dynamics.dynEntourage_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_antitone (T : X -> X) (U : SetRel X X) : Antitone (fun n : Na
t => dynEntourage T U n)
参数：T : X -> X；U : SetRel X X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_mono'`：iInter₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i' j', exists i j, s i j subseteq t i' j') : ⋂
 (i) (j…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma dynEntourage_antitone (T : X → X) (U : SetRel X X) :
    Antitone (fun n : ℕ ↦ dynEntourage T U n) :=
  fun m n m_n ↦ iInter₂_mono' fun k k_m ↦ by use k, lt_of_lt_of_le k_m m_n

@[gcongr]
/-
**Dynamics.dynEntourage_mono** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_mono (hUV : U subseteq V) (hmn : m <= n) : dynEntourage T U n
 subseteq dynEntourage T V m
参数：hUV : U subseteq V；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.dynEntourage_monotone`：dynEntourage_monotone (T : X -> X) (n : 
Nat) : Monotone (fun U : SetRel X X => dynEntourage T U n)
· 使用引理 `Dynamics.dynEntourage_antitone`：dynEntourage_antitone (T : X -> X) (U : 
SetRel X X) : Antitone (fun n : Nat => dynEntourage T U n)
-/
lemma dynEntourage_mono (hUV : U ⊆ V) (hmn : m ≤ n) : dynEntourage T U n ⊆ dynEntourage T V m :=
  (dynEntourage_monotone _ _ hUV).trans (dynEntourage_antitone _ _ hmn)
/-
**Dynamics.dynEntourage_zero** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X}, Dynamics.dynEntourage T U 0
 = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dynEntourage_zero : dynEntourage T U 0 = univ := by simp [dynEntourage]
/-
**Dynamics.dynEntourage_one** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X}, Dynamics.dynEntourage T U 1
 = U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dynEntourage_one : dynEntourage T U 1 = U := by simp [dynEntourage]

@[simp]
/-
**Dynamics.dynEntourage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：dynEntourage_univ {T : X -> X} {n : Nat} : dynEntourage T univ n = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dynEntourage_univ {T : X → X} {n : ℕ} :
    dynEntourage T univ n = univ := by simp [dynEntourage]
/-
**Dynamics.mem_ball_dynEntourage_comp** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：mem_ball_dynEntourage_comp (T : X -> X) (n : Nat) {U : SetRel X X} [U.IsSy
mm] (x y : X) (h : (ball x (dynEntourage T U n) inter ball y (dynEntourage T U n
)).Nonempty) : x in ball y (dynEntourage T (U ○ U) n)
参数：T : X -> X；n : Nat；x y : X；h : (ball x (dynEntourage T U n) inter ball y (dyn
Entourage T U n)).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Dynamics.dynEntourage_comp_subset`：dynEntourage_comp_subset (T : X -> X)
 (U V : SetRel X X) (n : Nat) : (dynEntourage T U n) ○ (dynEntourage T V n) subs
eteq dynEntourage T (U …
· 使用定理 `UniformSpace.mem_ball_comp`：mem_ball_comp {V W : Set (β × β)} {x y z} (h
 : y in ball x V) (h' : z in ball y W) : z in ball x (V ○ W)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
-/
lemma mem_ball_dynEntourage_comp (T : X → X) (n : ℕ) {U : SetRel X X} [U.IsSymm]
    (x y : X) (h : (ball x (dynEntourage T U n) ∩ ball y (dynEntourage T U n)).Nonempty) :
    x ∈ ball y (dynEntourage T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)
/-
**Dynamics._root_.Function.Semiconj.preimage_dynEntourage** 是 Mathlib 中的一个引理，位于命
名空间 `Dynamics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Semiconj.preimage_dynEntourage {Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (map φ φ) ⁻¹' (dynEntourage T U n) = dynEntourage S ((map φ φ) ⁻¹' U) n := by
  rw [dynEntourage, preimage_iInter₂]
  refine iInter₂_congr fun k _ ↦ ?_
  rw [← preimage_comp, ← preimage_comp, map_iterate S S k, map_iterate T T k, map_comp_map,
    map_comp_map, (Function.Semiconj.iterate_right h k).comp_eq]

end Dynamics

