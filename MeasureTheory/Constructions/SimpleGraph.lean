/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Sigma-algebra on simple graphs

In this file, we pull back the sigma-algebra on `V → V → Prop` to a sigma-algebra on
`SimpleGraph V` and prove that common operations are measurable.
-/

public section

open MeasureTheory
open scoped Finset

namespace SimpleGraph
variable {V : Type*}

/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MeasurableSpace (SimpleGraph V) := .comap Adj inferInstance

/-- A simple graph-valued map is measurable iff all induced adjacency maps are measurable. -/
/-
**SimpleGraph.measurable_iff_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：measurable_iff_adj {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω -> SimpleGra
ph V} : Measurable G ↔ forall u v, Measurable fun ω => (G ω).Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A simple graph-valued map is measurable iff all induced adjacency maps are measu
rable.
-/
lemma measurable_iff_adj {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω → SimpleGraph V} :
    Measurable G ↔ ∀ u v, Measurable fun ω ↦ (G ω).Adj u v := by
  simp [measurable_comap_iff, measurable_pi_iff]

@[fun_prop]
/-
**SimpleGraph.measurable_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：measurable_adj : Measurable (Adj : SimpleGraph V -> V -> V -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma measurable_adj : Measurable (Adj : SimpleGraph V → V → V → Prop) := comap_measurable _

@[fun_prop]
/-
**SimpleGraph.measurable_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：measurable_edgeSet : Measurable (edgeSet : SimpleGraph V -> Set (Sym2 V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `measurable_set_iff`：measurable_set_iff : Measurable g ↔ forall a, Measur
able fun x => a in g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用引理 `SimpleGraph.measurable_adj`：measurable_adj : Measurable (Adj : SimpleGra
ph V -> V -> V -> Prop)
-/
lemma measurable_edgeSet : Measurable (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  measurable_set_iff.2 <| by rintro ⟨u, v⟩; simp only [mem_edgeSet]; fun_prop

@[simp, fun_prop]
/-
**SimpleGraph.measurable_fromEdgeSet** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：measurable_fromEdgeSet : Measurable (fromEdgeSet : Set (Sym2 V) -> SimpleG
raph V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Measurable.and`：Measurable.and (hp : Measurable p) (hq : Measurable q) :
 Measurable fun a => p a ∧ q a
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma measurable_fromEdgeSet : Measurable (fromEdgeSet : Set (Sym2 V) → SimpleGraph V) := by
  simp only [measurable_iff_adj, fromEdgeSet_adj, ne_eq]; fun_prop
/-
**SimpleGraph.measurableEmbedding_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：measurableEmbedding_edgeSet [Countable V] : MeasurableEmbedding (edgeSet :
 SimpleGraph V -> Set (Sym2 V)) where injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.edgeSet_injective`：edgeSet_injective : Injective (edgeSet : 
SimpleGraph V -> Set (Sym2 V))
· 使用引理 `SimpleGraph.measurable_edgeSet`：measurable_edgeSet : Measurable (edgeSet
 : SimpleGraph V -> Set (Sym2 V))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Measurable.and`：Measurable.and (hp : Measurable p) (hq : Measurable q) :
 Measurable fun a => p a ∧ q a
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSet.mem`：∀ {α : Type u_1} {s : Set α} [inst : MeasurableSpace 
α], MeasurableSet s → Measurable fun x => x ∈ s
· 使用引理 `SimpleGraph.measurable_fromEdgeSet`：measurable_fromEdgeSet : Measurable 
(fromEdgeSet : Set (Sym2 V) -> SimpleGraph V)
· 使用引理 `Measurable.forall`：Measurable.forall [Countable ι] {p : ι -> α -> Prop} 
(hp : forall i, Measurable (p i)) : Measurable fun a => forall i, p i a
· 使用定理 `Quotient.countable`：∀ {α : Sort u} [Countable α] {r : α → α → Prop}, Cou
ntable (Quot r)
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用引理 `Measurable.imp`：Measurable.imp (hp : Measurable p) (hq : Measurable q) :
 Measurable fun a => p a -> q a
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用引理 `Measurable.not`：Measurable.not (hp : Measurable p) : Measurable (¬ p ·)
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
-/
lemma measurableEmbedding_edgeSet [Countable V] :
    MeasurableEmbedding (edgeSet : SimpleGraph V → Set (Sym2 V)) where
  injective := edgeSet_injective
  measurable := measurable_edgeSet
  measurableSet_image' s hs := by
    simp only [← measurable_mem, Set.mem_image, edgeSet_eq_iff, ↓existsAndEq, true_and,
      Set.disjoint_right]
    refine .and (hs.mem.comp measurable_fromEdgeSet) <| .forall fun e ↦ .imp ?_ ?_ <;> fun_prop

end SimpleGraph

