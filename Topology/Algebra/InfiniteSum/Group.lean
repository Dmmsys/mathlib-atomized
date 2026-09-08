/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Infinite sums and products in topological groups

Lemmas on topological sums in groups (as opposed to monoids).
-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}

section IsTopologicalGroup

variable [CommGroup α] [TopologicalSpace α] [IsTopologicalGroup α]
variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive]
/-
**HasProd.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹) a⁻¹ L
参数：h : HasProd f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comm
Monoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilt
e…
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem HasProd.inv (h : HasProd f a L) : HasProd (fun b ↦ (f b)⁻¹) a⁻¹ L := by
  simpa only using! h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]
/-
**Multipliable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.inv (hf : Multipliable f L) : Multipliable (fun b => (f b)⁻¹)
 L
参数：hf : Multipliable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.inv`：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹
) a⁻¹ L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.inv (hf : Multipliable f L) : Multipliable (fun b ↦ (f b)⁻¹) L :=
  hf.hasProd.inv.multipliable

@[to_additive]
/-
**Multipliable.of_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.of_inv (hf : Multipliable (fun b => (f b)⁻¹) L) : Multipliabl
e f L
参数：hf : Multipliable (fun b => (f b)⁻¹) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Multipliable.inv`：Multipliable.inv (hf : Multipliable f L) : Multipliabl
e (fun b => (f b)⁻¹) L
-/
theorem Multipliable.of_inv (hf : Multipliable (fun b ↦ (f b)⁻¹) L) : Multipliable f L := by
  simpa only [inv_inv] using hf.inv

@[to_additive]
/-
**multipliable_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_inv_iff : (Multipliable (fun b => (f b)⁻¹) L) ↔ Multipliable 
f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.of_inv`：Multipliable.of_inv (hf : Multipliable (fun b => (f
 b)⁻¹) L) : Multipliable f L
· 使用定理 `Multipliable.inv`：Multipliable.inv (hf : Multipliable f L) : Multipliabl
e (fun b => (f b)⁻¹) L
-/
theorem multipliable_inv_iff : (Multipliable (fun b ↦ (f b)⁻¹) L) ↔ Multipliable f L :=
  ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]
/-
**HasProd.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : HasProd (fun b =
> f b / g b) (a₁ / a₂) L
参数：hf : HasProd f a₁ L；hg : HasProd g a₂ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `HasProd.inv`：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹
) a⁻¹ L
-/
theorem HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) :
    HasProd (fun b ↦ f b / g b) (a₁ / a₂) L := by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]
/-
**Multipliable.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.div (hf : Multipliable f L) (hg : Multipliable g L) : Multipl
iable (fun b => f b / g b) L
参数：hf : Multipliable f L；hg : Multipliable g L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.div`：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : H
asProd (fun b => f b / g b) (a₁ / a₂) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.div (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b ↦ f b / g b) L :=
  (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]
/-
**Multipliable.trans_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.trans_div (hg : Multipliable g L) (hfg : Multipliable (fun b 
=> f b / g b) L) : Multipliable f L
参数：hg : Multipliable g L；hfg : Multipliable (fun b => f b / g b) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `Multipliable.mul`：Multipliable.mul (hf : Multipliable f L) (hg : Multipl
iable g L) : Multipliable (fun b => f b * g b) L
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem Multipliable.trans_div (hg : Multipliable g L) (hfg : Multipliable (fun b ↦ f b / g b) L) :
    Multipliable f L := by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]
/-
**multipliable_iff_of_multipliable_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_iff_of_multipliable_div (hfg : Multipliable (fun b => f b / g
 b) L) : Multipliable f L ↔ Multipliable g L
参数：hfg : Multipliable (fun b => f b / g b) L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.trans_div`：Multipliable.trans_div (hg : Multipliable g L) (
hfg : Multipliable (fun b => f b / g b) L) : Multipliable f L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Multipliable.inv`：Multipliable.inv (hf : Multipliable f L) : Multipliabl
e (fun b => (f b)⁻¹) L
-/
theorem multipliable_iff_of_multipliable_div (hfg : Multipliable (fun b ↦ f b / g b) L) :
    Multipliable f L ↔ Multipliable g L :=
  ⟨fun hf ↦ hf.trans_div <| by simpa only [inv_div] using hfg.inv, fun hg ↦ hg.trans_div hfg⟩

@[to_additive]
/-
**HasProd.update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β) [DecidableEq β] (
a : α) : HasProd (update f b a) (a / f b * a₁) L
参数：hf : HasProd f a₁ L；b : β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `hasProd_ite_eq`：hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (
L
-/
theorem HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β) [DecidableEq β] (a : α) :
    HasProd (update f b a) (a / f b * a₁) L := by
  convert! (hasProd_ite_eq b (a / f b) (L := L)).mul hf with b'
  by_cases h : b' = b
  · rw [h, update_self]
    simp
  · simp only [h, update_of_ne, if_false, Ne, one_mul, not_false_iff]

@[to_additive]
/-
**Multipliable.update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.update [L.LeAtTop] (hf : Multipliable f L) (b : β) [Decidable
Eq β] (a : α) : Multipliable (update f b a) L
参数：hf : Multipliable f L；b : β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.update`：HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β)
 [DecidableEq β] (a : α) : HasProd (update f b a) (a / f b * a₁) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.update [L.LeAtTop] (hf : Multipliable f L) (b : β) [DecidableEq β] (a : α) :
    Multipliable (update f b a) L :=
  (hf.hasProd.update b a).multipliable

@[to_additive]
/-
**HasProd.hasProd_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁)
 : HasProd (f ∘ (↑) : ↑sᶜ -> α) a₂ ↔ HasProd f (a₁ * a₂)
参数：hf : HasProd (f ∘ (↑) : s -> α) a₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
· 使用定理 `Set.mulIndicator_compl`：mulIndicator_compl (s : Set α) (f : α -> G) : mu
lIndicator sᶜ f = f * (mulIndicator s f)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `HasProd.div`：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : H
asProd (fun b => f b / g b) (a₁ / a₂) L
-/
theorem HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd (f ∘ (↑) : ↑sᶜ → α) a₂ ↔ HasProd f (a₁ * a₂) := by
  refine ⟨fun h ↦ hf.mul_compl h, fun h ↦ ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using! h.div hf

@[to_additive]
/-
**HasProd.hasProd_iff_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁)
 : HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ -> α) (a₂ / a₁)
参数：hf : HasProd (f ∘ (↑) : s -> α) a₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `HasProd.hasProd_compl_iff`：HasProd.hasProd_compl_iff {s : Set β} (hf : H
asProd (f ∘ (↑) : s -> α) a₁) : HasProd (f ∘ (↑) : ↑sᶜ -> α) a₂ ↔ HasProd f (a₁ 
* a₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ → α) (a₂ / a₁) :=
  Iff.symm <| hf.hasProd_compl_iff.trans <| by rw [mul_div_cancel]

@[to_additive]
/-
**Multipliable.multipliable_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑
) : s -> α)) : Multipliable (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f where mp
参数：hf : Multipliable (f ∘ (↑) : s -> α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HasProd.hasProd_compl_iff`：HasProd.hasProd_compl_iff {s : Set β} (hf : H
asProd (f ∘ (↑) : s -> α) a₁) : HasProd (f ∘ (↑) : ↑sᶜ -> α) a₂ ↔ HasProd f (a₁ 
* a₂)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `HasProd.hasProd_iff_compl`：HasProd.hasProd_iff_compl {s : Set β} (hf : H
asProd (f ∘ (↑) : s -> α) a₁) : HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ -> α) (a₂ 
/ a₁)
-/
theorem Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑) : s → α)) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f where
  mp := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]
/-
**Finset.hasProd_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : Topological
Space α] [IsTopologicalGroup α] {f : β → α}   {a : α} (s : Finset β), HasProd (f
un x => f ↑x) a ↔ HasProd f (a * ∏ i ∈ s, f i)
参数：s : Finset β；fun x => f ↑x；a * ∏ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `HasProd.hasProd_compl_iff`：HasProd.hasProd_compl_iff {s : Set β} (hf : H
asProd (f ∘ (↑) : s -> α) a₁) : HasProd (f ∘ (↑) : ↑sᶜ -> α) a₂ ↔ HasProd f (a₁ 
* a₂)
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem Finset.hasProd_compl_iff (s : Finset β) :
    HasProd (fun x : { x // x ∉ s } ↦ f x) a ↔ HasProd f (a * ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_compl_iff.trans <| by rw [mul_comm]

@[to_additive]
/-
**Finset.hasProd_iff_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : Topological
Space α] [IsTopologicalGroup α] {f : β → α}   {a : α} (s : Finset β), HasProd f 
a ↔ HasProd (fun x => f ↑x) (a / ∏ i ∈ s, f i)
参数：s : Finset β；fun x => f ↑x；a / ∏ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.hasProd_iff_compl`：HasProd.hasProd_iff_compl {s : Set β} (hf : H
asProd (f ∘ (↑) : s -> α) a₁) : HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ -> α) (a₂ 
/ a₁)
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
protected theorem Finset.hasProd_iff_compl (s : Finset β) :
    HasProd f a ↔ HasProd (fun x : { x // x ∉ s } ↦ f x) (a / ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_iff_compl

@[to_additive]
/-
**Finset.multipliable_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : Topological
Space α] [IsTopologicalGroup α] {f : β → α}   (s : Finset β), (Multipliable fun 
x => f ↑x) ↔ Multipliable f
参数：s : Finset β；Multipliable fun x => f ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.multipliable_compl_iff`：Multipliable.multipliable_compl_iff
 {s : Set β} (hf : Multipliable (f ∘ (↑) : s -> α)) : Multipliable (f ∘ (↑) : ↑s
ᶜ -> α) ↔ Multipliable f …
· 使用定理 `Finset.multipliable`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid 
α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   Multipliable (f ∘
 Subtype.…
-/
protected theorem Finset.multipliable_compl_iff (s : Finset β) :
    (Multipliable fun x : { x // x ∉ s } ↦ f x) ↔ Multipliable f :=
  (s.multipliable f).multipliable_compl_iff

@[to_additive]
/-
**Set.Finite.multipliable_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) : Multipliab
le (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.multipliable_compl_iff`：Multipliable.multipliable_compl_iff
 {s : Set β} (hf : Multipliable (f ∘ (↑) : s -> α)) : Multipliable (f ∘ (↑) : ↑s
ᶜ -> α) ↔ Multipliable f …
· 使用定理 `Set.Finite.multipliable`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMon
oid α] [inst_1 : TopologicalSpace α] {s : Set β},   s.Finite → ∀ (f : β → α), Mu
ltipliable (f…
-/
theorem Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f :=
  (hs.multipliable f).multipliable_compl_iff

@[to_additive]
/-
**hasProd_ite_div_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_ite_div_hasProd [L.LeAtTop] [DecidableEq β] (hf : HasProd f a L) (
b : β) : HasProd (fun n => ite (n = b) 1 (f n)) (a / f b) L
参数：hf : HasProd f a L；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasProd.update`：HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β)
 [DecidableEq β] (a : α) : HasProd (update f b a) (a / f b * a₁) L
-/
theorem hasProd_ite_div_hasProd [L.LeAtTop] [DecidableEq β] (hf : HasProd f a L) (b : β) :
    HasProd (fun n ↦ ite (n = b) 1 (f n)) (a / f b) L := by
  convert! hf.update b 1 using 1
  · ext n
    rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]

/-- A more general version of `Multipliable.congr`, allowing the functions to
disagree on a finite set.

Note that this requires the target to be a group, and hence fails for products valued
in a ring. See `Multipliable.congr_cofinite₀` for a version applying in this case,
with an additional non-vanishing hypothesis.
-/
@[to_additive /-- A more general version of `Summable.congr`, allowing the functions to
disagree on a finite set. -/]
/-
**Multipliable.congr_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.congr_cofinite (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g)
 : Multipliable g
参数：hf : Multipliable f；hfg : f =ᶠ[cofinite] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.multipliable_compl_iff`：Set.Finite.multipliable_compl_iff {s 
: Set β} (hs : s.Finite) : Multipliable (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f
· 使用定理 `Multipliable.congr`：Multipliable.congr (hf : Multipliable f L) (hfg : fo
rall b, f b = g b) : Multipliable g L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Multipliable.congr_cofinite (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g) :
    Multipliable g :=
  hfg.multipliable_compl_iff.mp <| (hfg.multipliable_compl_iff.mpr hf).congr (by simp)

/-- A more general version of `multipliable_congr`, allowing the functions to
disagree on a finite set. -/
@[to_additive /-- A more general version of `summable_congr`, allowing the functions to
disagree on a finite set. -/]
/-
**multipliable_congr_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_congr_cofinite (hfg : f =ᶠ[cofinite] g) : Multipliable f ↔ Mu
ltipliable g
参数：hfg : f =ᶠ[cofinite] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.congr_cofinite`：Multipliable.congr_cofinite (hf : Multiplia
ble f) (hfg : f =ᶠ[cofinite] g) : Multipliable g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem multipliable_congr_cofinite (hfg : f =ᶠ[cofinite] g) :
    Multipliable f ↔ Multipliable g :=
  ⟨fun h ↦ h.congr_cofinite hfg, fun h ↦ h.congr_cofinite (hfg.mono fun _ h' ↦ h'.symm)⟩

@[to_additive]
/-
**Multipliable.congr_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.congr_atTop {f₁ g₁ : Nat -> α} (hf : Multipliable f₁) (hfg : 
f₁ =ᶠ[atTop] g₁) : Multipliable g₁
参数：hf : Multipliable f₁；hfg : f₁ =ᶠ[atTop] g₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.congr_cofinite`：Multipliable.congr_cofinite (hf : Multiplia
ble f) (hfg : f =ᶠ[cofinite] g) : Multipliable g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem Multipliable.congr_atTop {f₁ g₁ : ℕ → α} (hf : Multipliable f₁) (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable g₁ := hf.congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

@[to_additive]
/-
**multipliable_congr_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_congr_atTop {f₁ g₁ : Nat -> α} (hfg : f₁ =ᶠ[atTop] g₁) : Mult
ipliable f₁ ↔ Multipliable g₁
参数：hfg : f₁ =ᶠ[atTop] g₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multipliable_congr_cofinite`：multipliable_congr_cofinite (hfg : f =ᶠ[cof
inite] g) : Multipliable f ↔ Multipliable g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem multipliable_congr_atTop {f₁ g₁ : ℕ → α} (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable f₁ ↔ Multipliable g₁ := multipliable_congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

section tprod

variable [T2Space α]

@[to_additive]
/-
**tprod_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_inv : ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsClosedEmbedding.map_tprod`：Topology.IsClosedEmbedding.map_tpr
od {ι α α' G : Type*} [CommMonoid α] [CommMonoid α'] [TopologicalSpace α] [Topol
ogicalSpace α'] [T2Space α…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem tprod_inv : ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹ :=
  ((Homeomorph.inv α).isClosedEmbedding.map_tprod f (g := MulEquiv.inv α)).symm

@[to_additive]
/-
**Multipliable.tprod_div** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [inst : CommGroup 
α] [inst_1 : TopologicalSpace α]   [IsTopologicalGroup α] {f g : β → α} [T2Space
 α] [L.NeBot],   Multipliable f L → Multipliable g L → ∏'[L] (b : β), f b / g b 
= (∏'[L] (b : β), f b) / ∏'[L] (b : β), g b
参数：b : β；∏'[L] (b : β), f b；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `HasProd.div`：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : H
asProd (fun b => f b / g b) (a₁ / a₂) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_div [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b / g b) = (∏'[L] b, f b) / ∏'[L] b, g b :=
  (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]
/-
**Multipliable.prod_mul_tprod_compl** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : Topological
Space α] [IsTopologicalGroup α] {f : β → α}   [T2Space α] {s : Finset β}, Multip
liable f → (∏ x ∈ s, f x) * ∏' (x : ↑(↑s)ᶜ), f ↑x = ∏' (x : β), f x
参数：∏ x ∈ s, f x；x : ↑(↑s)ᶜ；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.multipliable_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : C
ommGroup α] [inst_1 : TopologicalSpace α] [IsTopologicalGroup α] {f : β → α}   (
s : Finset β), (Mul…
-/
protected theorem Multipliable.prod_mul_tprod_compl {s : Finset β} (hf : Multipliable f) :
    (∏ x ∈ s, f x) * ∏' x : ↑(s : Set β)ᶜ, f x = ∏' x, f x :=
  ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm

/-- Let `f : β → α` be a multipliable function and let `b ∈ β` be an index.
Lemma `tprod_eq_mul_tprod_ite` writes `∏ n, f n` as `f b` times the product of the
remaining terms. -/
@[to_additive /-- Let `f : β → α` be a summable function and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ' n, f n` as `f b` plus the sum of the
remaining terms. -/]
/-
**Multipliable.tprod_eq_mul_tprod_ite** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : Topological
Space α] [IsTopologicalGroup α] {f : β → α}   [T2Space α] [inst_4 : DecidableEq 
β],   Multipliable f → ∀ (b : β), ∏' (n : β), f n = f b * ∏' (n : β), if n = b t
hen 1 else f n
参数：b : β；n : β；n : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasProd_ite_div_hasProd`：hasProd_ite_div_hasProd [L.LeAtTop] [DecidableE
q β] (hf : HasProd f a L) (b : β) : HasProd (fun n => ite (n = b) 1 (f n)) (a / 
f b) L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
-/
protected theorem Multipliable.tprod_eq_mul_tprod_ite [DecidableEq β] (hf : Multipliable f)
    (b : β) : ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) := by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm

end tprod

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace α]

/-- The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test** -/
@[to_additive /-- The **Cauchy criterion** for infinite sums, also known as the
**Cauchy convergence test** -/]
/-
**multipliable_iff_cauchySeq_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_iff_cauchySeq_finset [CommMonoid α] [CompleteSpace α] {f : β 
-> α} : Multipliable f ↔ CauchySeq fun s : Finset β => ∏ b in s, f b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `cauchy_map_iff_exists_tendsto`：cauchy_map_iff_exists_tendsto [CompleteSp
ace α] {l : Filter β} {f : β -> α} [NeBot l] : Cauchy (l.map f) ↔ exists x, Tend
sto f l (𝓝 x)
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem multipliable_iff_cauchySeq_finset [CommMonoid α] [CompleteSpace α] {f : β → α} :
    Multipliable f ↔ CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b := by
  exact cauchy_map_iff_exists_tendsto.symm

variable [CommGroup α] [IsUniformGroup α] {f g : β → α}

@[to_additive]
/-
**cauchySeq_finset_iff_prod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_iff_prod_vanishing : (CauchySeq fun s : Finset β => ∏ b i
n s, f b) ↔ forall e in 𝓝 (1 : α), exists s : Finset β, forall t, Disjoint t s -
> (∏ b in t, f b) in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `uniformity_eq_comap_nhds_one`：uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = coma
p (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `exists_nhds_split_inv`：exists_nhds_split_inv {s : Set G} (hs : s in 𝓝 (1
 : G)) : exists V in 𝓝 (1 : G), forall v in V, forall w in V, v / w in s
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `mul_div_mul_right_eq_div`：mul_div_mul_right_eq_div (a b c : G) : a * c /
 (b * c) = a / b
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
-/
theorem cauchySeq_finset_iff_prod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  classical
  simp only [CauchySeq, cauchy_map_iff, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, Function.comp_def, atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∏ b ∈ t₂, f b) / ∏ b ∈ t₁, f b) = (∏ b ∈ t₂ \ s, f b) / ∏ b ∈ t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁, ← Finset.prod_sdiff ht₂, mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

@[to_additive]
/-
**cauchySeq_finset_iff_tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_iff_tprod_vanishing : (CauchySeq fun s : Finset β => ∏ b 
in s, f b) ↔ forall e in 𝓝 (1 : α), exists s : Finset β, forall t : Set β, Disjo
int t s -> (∏' b : t, f b) in e
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
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subtype_map_embedding`：prod_subtype_map_embedding {p : ι -> 
Prop} {s : Finset { x // p x }} {f : { x // p x } -> M} {g : ι -> M} (h : forall
 x : { x // p x }, x in…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `Finset.tprod_subtype`：Finset.tprod_subtype (s : Finset β) (f : β -> α) :
 ∏' x : { x // x in s }, f x = ∏ x in s, f x
-/
theorem cauchySeq_finset_iff_tprod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts ↦ oe ?_⟩
    by_cases ht : Multipliable fun a : t ↦ f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasProd (Eventually.of_forall fun t' ↦ ?_)
      rw [← prod_subtype_map_embedding fun _ _ ↦ by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts ↦ (t.tprod_subtype f).symm ▸ hs _ hts⟩

variable [CompleteSpace α]

@[to_additive]
/-
**multipliable_iff_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_iff_vanishing : Multipliable f ↔ forall e in 𝓝 (1 : α), exist
s s : Finset β, forall t, Disjoint t s -> (∏ b in t, f b) in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multipliable_iff_cauchySeq_finset`：multipliable_iff_cauchySeq_finset [Co
mmMonoid α] [CompleteSpace α] {f : β -> α} : Multipliable f ↔ CauchySeq fun s : 
Finset β => ∏ b in s, f…
· 使用定理 `cauchySeq_finset_iff_prod_vanishing`：cauchySeq_finset_iff_prod_vanishing
 : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exists
 s : Finset β, forall t, …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem multipliable_iff_vanishing :
    Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_prod_vanishing]

@[to_additive]
/-
**multipliable_iff_tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_iff_tprod_vanishing : Multipliable f ↔ forall e in 𝓝 (1 : α),
 exists s : Finset β, forall t : Set β, Disjoint t s -> (∏' b : t, f b) in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multipliable_iff_cauchySeq_finset`：multipliable_iff_cauchySeq_finset [Co
mmMonoid α] [CompleteSpace α] {f : β -> α} : Multipliable f ↔ CauchySeq fun s : 
Finset β => ∏ b in s, f…
· 使用定理 `cauchySeq_finset_iff_tprod_vanishing`：cauchySeq_finset_iff_tprod_vanishi
ng : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exis
ts s : Finset β, forall t …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem multipliable_iff_tprod_vanishing : Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_tprod_vanishing]

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
@[to_additive]
/-
**Multipliable.multipliable_of_eq_one_or_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f) (h : for
all b, g b = 1 ∨ g b = f b) : Multipliable g
参数：hf : Multipliable f；h : forall b, g b = 1 ∨ g b = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multipliable_iff_vanishing`：multipliable_iff_vanishing : Multipliable f 
↔ forall e in 𝓝 (1 : α), exists s : Finset β, forall t, Disjoint t s -> (∏ b in 
t, f b) in e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq 
u) (d : Disjoint u t) : Disjoint s t
-/
theorem Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f)
    (h : ∀ b, g b = 1 ∨ g b = f b) : Multipliable g := by
  classical
  exact multipliable_iff_vanishing.2 fun e he ↦
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht ↦
      have eq : ∏ b ∈ t with g b = f b, f b = ∏ b ∈ t, g b :=
        calc
          ∏ b ∈ t with g b = f b, f b = ∏ b ∈ t with g b = f b, g b :=
            Finset.prod_congr rfl fun b hb ↦ (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b ∈ t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]
/-
**Multipliable.mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : CommGrou
p α] [IsUniformGroup α] {f : β → α}   [CompleteSpace α], Multipliable f → ∀ (s :
 Set β), Multipliable (s.mulIndicator f)
参数：s : Set β；s.mulIndicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.multipliable_of_eq_one_or_self`：Multipliable.multipliable_o
f_eq_one_or_self (hf : Multipliable f) (h : forall b, g b = 1 ∨ g b = f b) : Mul
tipliable g
· 使用引理 `Set.mulIndicator_eq_one_or_self`：mulIndicator_eq_one_or_self (s : Set α)
 (f : α -> M) (a : α) : mulIndicator s f a = 1 ∨ mulIndicator s f a = f a
-/
protected theorem Multipliable.mulIndicator (hf : Multipliable f) (s : Set β) :
    Multipliable (s.mulIndicator f) :=
  hf.multipliable_of_eq_one_or_self <| Set.mulIndicator_eq_one_or_self _ _

@[to_additive]
/-
**Multipliable.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.comp_injective {i : γ -> β} (hf : Multipliable f) (hi : Injec
tive i) : Multipliable (f ∘ i)
参数：hf : Multipliable f；hi : Injective i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_range_comp`：mulIndicator_range_comp {ι : Sort*} (f : ι 
-> α) (g : α -> M) : mulIndicator (range f) g ∘ f = g ∘ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.multipliable_iff`：Function.Injective.multipliable_iff
 {g : γ -> β} (hg : Injective g) (hf : forall x ∉ Set.range g, f x = 1) : Multip
liable (f ∘ g) ↔ Multipli…
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `Multipliable.mulIndicator`：∀ {α : Type u_1} {β : Type u_2} [inst : Unifo
rmSpace α] [inst_1 : CommGroup α] [IsUniformGroup α] {f : β → α}   [CompleteSpac
e α], Multiplia…
-/
theorem Multipliable.comp_injective {i : γ → β} (hf : Multipliable f) (hi : Injective i) :
    Multipliable (f ∘ i) := by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx ↦ Set.mulIndicator_of_notMem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]
/-
**Multipliable.subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.subtype (hf : Multipliable f) (p : β -> Prop) : Multipliable 
(f ∘ (↑) : Subtype p -> α)
参数：hf : Multipliable f；p : β -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem Multipliable.subtype (hf : Multipliable f) (p : β → Prop) :
    Multipliable (f ∘ (↑) : Subtype p → α) :=
  hf.comp_injective Subtype.coe_injective

@[to_additive]
/-
**multipliable_subtype_and_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_subtype_and_compl {s : Set β} : ((Multipliable fun x : s => f
 x) ∧ Multipliable fun x : ↑sᶜ => f x) ↔ Multipliable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Multipliable.mul_compl`：Multipliable.mul_compl {s : Set β} (hs : Multipl
iable (f ∘ (↑) : s -> α)) (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α)) : M
ultipliable …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
-/
theorem multipliable_subtype_and_compl {s : Set β} :
    ((Multipliable fun x : s ↦ f x) ∧ Multipliable fun x : ↑sᶜ ↦ f x) ↔ Multipliable f :=
  ⟨and_imp.2 Multipliable.mul_compl, fun h ↦ ⟨h.subtype (· ∈ s), h.subtype (· ∈ sᶜ)⟩⟩

@[to_additive]
/-
**Multipliable.tprod_subtype_mul_tprod_subtype_compl** 是 Mathlib 中的一个定理，位于命名空间 `
Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : CommGrou
p α] [IsUniformGroup α] [CompleteSpace α]   [T2Space α] {f : β → α}, Multipliabl
e f → ∀ (s : Set β), (∏' (x : ↑s), f ↑x) * ∏' (x : ↑sᶜ), f ↑x = ∏' (x : β), f x
参数：s : Set β；∏' (x : ↑s), f ↑x；x : ↑sᶜ；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.unique`：HasProd.unique {a₁ a₂ : α} : HasProd f a₁ L -> HasProd f
 a₂ L -> a₁ = a₂
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.mul_compl`：HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) 
: s -> α) a) (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
-/
protected theorem Multipliable.tprod_subtype_mul_tprod_subtype_compl [T2Space α] {f : β → α}
    (hf : Multipliable f) (s : Set β) : (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  ((hf.subtype _).hasProd.mul_compl (hf.subtype _).hasProd).unique hf.hasProd

@[to_additive]
/-
**Multipliable.prod_mul_tprod_subtype_compl** 是 Mathlib 中的一个定理，位于命名空间 `Multiplia
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : CommGrou
p α] [IsUniformGroup α] [CompleteSpace α]   [T2Space α] {f : β → α},   Multiplia
ble f → ∀ (s : Finset β), (∏ x ∈ s, f x) * ∏' (x : { x // x ∉ s }), f ↑x = ∏' (x
 : β), f x
参数：s : Finset β；∏ x ∈ s, f x；x : { x // x ∉ s }；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.tprod_subtype_mul_tprod_subtype_compl`：∀ {α : Type u_1} {β 
: Type u_2} [inst : UniformSpace α] [inst_1 : CommGroup α] [IsUniformGroup α] [C
ompleteSpace α]   [T2Space α] {f : β → α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.tprod_subtype'`：Finset.tprod_subtype' (s : Finset β) (f : β -> α)
 : ∏' x : (s : Set β), f x = ∏ x in s, f x
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
protected theorem Multipliable.prod_mul_tprod_subtype_compl [T2Space α] {f : β → α}
    (hf : Multipliable f) (s : Finset β) :
    (∏ x ∈ s, f x) * ∏' x : { x // x ∉ s }, f x = ∏' x, f x := by
  rw [← hf.tprod_subtype_mul_tprod_subtype_compl s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl

end IsUniformGroup

section IsTopologicalGroup

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] {f : α → G}

@[to_additive]
/-
**Multipliable.vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e in 𝓝 (1 :
 G)) : exists s : Finset α, forall t, Disjoint t s -> (∏ k in t, f k) in e
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformGroup_of_commGroup`：isUniformGroup_of_commGroup : IsUniformGrou
p G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_finset_iff_prod_vanishing`：cauchySeq_finset_iff_prod_vanishing
 : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exists
 s : Finset β, forall t, …
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (1 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∏ k ∈ t, f k) ∈ e := by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
/-
**Multipliable.tprod_vanishing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.tprod_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e in 
𝓝 1) : exists s : Finset α, forall t : Set α, Disjoint t s -> (∏' b : t, f b) in
 e
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformGroup_of_commGroup`：isUniformGroup_of_commGroup : IsUniformGrou
p G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_finset_iff_tprod_vanishing`：cauchySeq_finset_iff_tprod_vanishi
ng : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔ forall e in 𝓝 (1 : α), exis
ts s : Finset β, forall t …
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.tprod_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 1) :
    ∃ s : Finset α, ∀ t : Set α, Disjoint t s → (∏' b : t, f b) ∈ e := by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

/-- The product over the complement of a finset tends to `1` when the finset grows to cover the
whole space. This does not need a multipliability assumption, as otherwise all such products are
one. -/
@[to_additive /-- The sum over the complement of a finset tends to `0` when the finset grows to
cover the whole space. This does not need a summability assumption, as otherwise all such sums are
zero. -/]
/-
**tendsto_tprod_compl_atTop_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_tprod_compl_atTop_one (f : α -> G) : Tendsto (fun s : Finset α => 
∏' a : { x // x ∉ s }, f a) atTop (𝓝 1)
参数：f : α -> G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_vanishing`：Multipliable.tprod_vanishing (hf : Multipl
iable f) ⦃e : Set G⦄ (he : e in 𝓝 1) : exists s : Finset α, forall t : Set α, Di
sjoint t s -> (∏' …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `Finset.multipliable_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : C
ommGroup α] [inst_1 : TopologicalSpace α] [IsTopologicalGroup α] {f : β → α}   (
s : Finset β), (Mul…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_tprod_compl_atTop_one (f : α → G) :
    Tendsto (fun s : Finset α ↦ ∏' a : { x // x ∉ s }, f a) atTop (𝓝 1) := by
  by_cases H : Multipliable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tprod_vanishing he
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
    exact ⟨s, fun t hts ↦ hs tᶜ <| Set.disjoint_left.mpr fun a ha has ↦ ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ ↦ (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [Finset.multipliable_compl_iff]

/-- Product divergence test: if `f` is unconditionally multipliable, then `f x` tends to one along
`cofinite`. -/
@[to_additive /-- Series divergence test: if `f` is unconditionally summable, then `f x` tends to
zero along `cofinite`. -/]
/-
**Multipliable.tendsto_cofinite_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofini
te (𝓝 1)
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Multipliable.vanishing`：Multipliable.vanishing (hf : Multipliable f) ⦃e 
: Set G⦄ (he : e in 𝓝 (1 : G)) : exists s : Finset α, forall t, Disjoint t s -> 
(∏ k in t, f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Finset.eventually_cofinite_notMem`：∀ {α : Type u_2} (s : Finset α), ∀ᶠ (
x : α) in Filter.cofinite, x ∉ s
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
-/
theorem Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofinite (𝓝 1) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_notMem.mono fun x hx ↦ ?_
  · simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]
/-
**Multipliable.hasFiniteMulSupport_of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Multipliable.hasFiniteMulSupport_of_discreteTopology {α : Type*} [CommGrou
p α] [TopologicalSpace α] [DiscreteTopology α] {β : Type*} (f : β -> α) (h : Mul
tipliable f) : HasFiniteMulSupport f
参数：f : β -> α；h : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `topologicalGroup_of_discreteTopology`：∀ {H : Type x} [inst : Topological
Space H] [inst_1 : Group H] [DiscreteTopology H], IsTopologicalGroup H
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `discreteTopology_iff_singleton_mem_nhds`：discreteTopology_iff_singleton_
mem_nhds [TopologicalSpace α] : DiscreteTopology α ↔ forall x : α, {x} in 𝓝 x
-/
theorem Multipliable.hasFiniteMulSupport_of_discreteTopology
    {α : Type*} [CommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    {β : Type*} (f : β → α) (h : Multipliable f) : HasFiniteMulSupport f :=
  haveI : IsTopologicalGroup α := ⟨⟩
  h.tendsto_cofinite_one (discreteTopology_iff_singleton_mem_nhds.mp ‹_› 1)

@[deprecated (since := "2026-03-03")] alias
  Multipliable.finite_mulSupport_of_discreteTopology :=
    Multipliable.hasFiniteMulSupport_of_discreteTopology

@[deprecated (since := "2026-03-03")] alias
  Summable.finite_support_of_discreteTopology :=
    Summable.hasFiniteSupport_of_discreteTopology

@[to_additive]
/-
**Multipliable.countable_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.countable_mulSupport [FirstCountableTopology G] [T1Space G] (
hf : Multipliable f) : f.mulSupport.Countable
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ker_nhds`：ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x}
· 使用定理 `Filter.Tendsto.countable_compl_preimage_ker`：∀ {α : Type u_2} {β : Type 
u_3} {f : α → β} {l : Filter β} [l.IsCountablyGenerated],   Filter.Tendsto f Fil
ter.cofinite l → (f ⁻¹' l.ker)ᶜ.C…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
-/
theorem Multipliable.countable_mulSupport [FirstCountableTopology G] [T1Space G]
    (hf : Multipliable f) : f.mulSupport.Countable := by
  simpa only [ker_nhds] using! hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]
/-
**multipliable_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_const_iff [Infinite β] [T2Space G] (a : G) : Multipliable (fu
n _ : β => a) ↔ a = 1
参数：a : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `compl_singleton_mem_nhds`：compl_singleton_mem_nhds [T1Space X] {x y : X}
 (h : y != x) : {x}ᶜ in 𝓝 y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
· 使用定理 `multipliable_one`：multipliable_one : Multipliable (fun _ => 1 : β -> α) 
L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem multipliable_const_iff [Infinite β] [T2Space G] (a : G) :
    Multipliable (fun _ : β ↦ a) ↔ a = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ ∈ 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
    exact not_finite β
  · rintro rfl
    exact multipliable_one

@[to_additive (attr := simp)]
/-
**tprod_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_const [T2Space G] (a : G) : ∏' _ : β, a = a ^ (Nat.card β)
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_prod`：tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉
 s, f b = 1) : ∏'[L] b, f b = ∏ b in s, f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
-/
theorem tprod_const [T2Space G] (a : G) : ∏' _ : β, a = a ^ (Nat.card β) := by
  rcases finite_or_infinite β with hβ | hβ
  · let : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx ↦ (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

end IsTopologicalGroup

section CommGroupWithZero

variable {K : Type*} [CommGroupWithZero K] [TopologicalSpace K]
  {f g : α → K} {L : SummationFilter α}

/-!
## Groups with a zero

These lemmas apply to a `CommGroupWithZero`; the most familiar case is when `K` is a field. These
are specific to the product setting and do not have a sensible additive analogue.
-/

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul K]

open Finset in
/-
**HasProd.congr_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HasProd.congr_cofinite₀ {c : K} (hc : HasProd f c) {s : Finset α}
    (hs : ∀ a ∈ s, f a ≠ 0) (hs' : ∀ a ∉ s, f a = g a) :
    HasProd g (c * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)) := by
  classical
  refine (Tendsto.mul_const ((∏ i ∈ s, g i) / ∏ i ∈ s, f i) hc).congr' ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i ∈ t, f i) * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)
  _ = ((∏ i ∈ s, f i) * ∏ i ∈ t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi ↦ hs' i (mem_sdiff.mp hi).2]
  _ = (∏ i ∈ s, g i) * ∏ i ∈ t \ s, g i := by
    rw [← mul_div_assoc, ← div_mul_eq_mul_div, ← div_mul_eq_mul_div, div_self, one_mul, mul_comm]
    exact prod_ne_zero_iff.mpr hs
  _ = ∏ i ∈ t, g i := by
    rw [← prod_union disjoint_sdiff, union_sdiff_of_subset ht]
/-
**Multipliable.tsum_congr_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Multipliable.tsum_congr_cofinite₀ [T2Space K] (hc : Multipliable f) {s : Finset α}
    (hs : ∀ a ∈ s, f a ≠ 0) (hs' : ∀ a ∉ s, f a = g a) :
    ∏' i, g i = ((∏' i, f i) * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)) :=
  (hc.hasProd.congr_cofinite₀ hs hs').tprod_eq

set_option backward.isDefEq.respectTransparency false in
/--
See also `Multipliable.congr_cofinite`, which does not have a non-vanishing condition, but instead
requires the target to be a group under multiplication (and hence fails for infinite products in a
ring).
-/
/-
**Multipliable.congr_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.congr_cofinite (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g)
 : Multipliable g
参数：hf : Multipliable f；hfg : f =ᶠ[cofinite] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.multipliable_compl_iff`：Set.Finite.multipliable_compl_iff {s 
: Set β} (hs : s.Finite) : Multipliable (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f
· 使用定理 `Multipliable.congr`：Multipliable.congr (hf : Multipliable f L) (hfg : fo
rall b, f b = g b) : Multipliable g L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
See also `Multipliable.congr_cofinite`, which does not have a non-vanishing cond
ition, but instead
requires the target to be a group under multiplication (and hence fails for infi
nite products in a
ring).
-/
lemma Multipliable.congr_cofinite₀ (hf : Multipliable f) (hf' : ∀ a, f a ≠ 0)
    (hfg : ∀ᶠ a in cofinite, f a = g a) :
    Multipliable g := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨s, hs⟩ : ∃ s : Finset α, ∀ i ∉ s, f i = g i := ⟨hfg.toFinset, by simp⟩
  exact (hc.congr_cofinite₀ (fun a _ ↦ hf' a) hs).multipliable

end SeparatelyContinuousMul

/-
**HasProd.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹) a⁻¹ L
参数：h : HasProd f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comm
Monoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilt
e…
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem HasProd.inv₀ {a : K} [ContinuousInv₀ K] (h : HasProd f a L) (ha : a ≠ 0) :
    HasProd (fun x ↦ (f x)⁻¹) a⁻¹ L := by
  simp_rw [HasProd, Finset.prod_inv_distrib]
  exact Tendsto.inv₀ h ha
/-
**Multipliable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.inv (hf : Multipliable f L) : Multipliable (fun b => (f b)⁻¹)
 L
参数：hf : Multipliable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.inv`：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹
) a⁻¹ L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.inv₀ [ContinuousInv₀ K] (h : Multipliable f L) (ne_zero : ∏'[L] x, f x ≠ 0) :
    Multipliable (fun x ↦ (f x)⁻¹) L :=
  h.hasProd.inv₀ ne_zero|>.multipliable
/-
**Multipliable.tprod_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Multipliable.tprod_inv₀ [ContinuousInv₀ K] [T2Space K] [L.NeBot]
    (h : Multipliable f L) (ne_zero : ∏'[L] x, f x ≠ 0) :
    ∏'[L] x, (f x)⁻¹ = (∏'[L] x, f x )⁻¹ :=
  h.hasProd.inv₀ ne_zero|>.tprod_eq
/-
**HasProd.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : HasProd (fun b =
> f b / g b) (a₁ / a₂) L
参数：hf : HasProd f a₁ L；hg : HasProd g a₂ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasProd.mul`：HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) : Has
Prod (fun b => f b * g b) (a * b) L
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `HasProd.inv`：HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹
) a⁻¹ L
-/
theorem HasProd.div₀ [ContinuousInv₀ K] [ContinuousMul K] {a b : K}
    (hf : HasProd f a L) (hg : HasProd g b L) (hb : b ≠ 0) :
    HasProd (fun x ↦ f x / g x) (a / b) L := by
  simp only [div_eq_mul_inv]
  exact hf.mul <| hg.inv₀ hb
/-
**Multipliable.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.div (hf : Multipliable f L) (hg : Multipliable g L) : Multipl
iable (fun b => f b / g b) L
参数：hf : Multipliable f L；hg : Multipliable g L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.div`：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : H
asProd (fun b => f b / g b) (a₁ / a₂) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.div₀ [ContinuousInv₀ K] [ContinuousMul K]
    (hf : Multipliable f L) (hg : Multipliable g L) (ne_zero : ∏'[L] x, g x ≠ 0) :
    Multipliable (fun x ↦ f x / g x) L :=
  hf.hasProd.div₀ hg.hasProd ne_zero|>.multipliable
/-
**Multipliable.tprod_div** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [inst : CommGroup 
α] [inst_1 : TopologicalSpace α]   [IsTopologicalGroup α] {f g : β → α} [T2Space
 α] [L.NeBot],   Multipliable f L → Multipliable g L → ∏'[L] (b : β), f b / g b 
= (∏'[L] (b : β), f b) / ∏'[L] (b : β), g b
参数：b : β；∏'[L] (b : β), f b；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `HasProd.div`：HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) : H
asProd (fun b => f b / g b) (a₁ / a₂) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.tprod_div₀ [ContinuousInv₀ K] [ContinuousMul K] [T2Space K] [L.NeBot]
    (hf : Multipliable f L) (hg : Multipliable g L) (ne_zero : ∏'[L] x, g x ≠ 0) :
    (∏'[L] x, f x / g x) = (∏'[L] x, f x) / (∏'[L] x, g x) :=
  hf.hasProd.div₀ hg.hasProd ne_zero|>.tprod_eq

end CommGroupWithZero

