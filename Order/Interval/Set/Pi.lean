/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

public section

-- Porting note: Added, since dot notation no longer works on `Function.update`
open Function

variable {ι : Type*} {α : ι → Type*}

namespace Set

section PiPreorder

variable [∀ i, Preorder (α i)] (x y : ∀ i, α i)

@[to_dual (attr := simp)]
/-
**Set.pi_univ_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ici : (pi univ fun i => Ici (x i)) = Ici x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_univ_Ici : (pi univ fun i ↦ Ici (x i)) = Ici x :=
  ext fun y ↦ by simp [Pi.le_def]

@[to_dual self, simp]
/-
**Set.pi_univ_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_univ_Icc : (pi univ fun i ↦ Icc (x i) (y i)) = Icc x y :=
  ext fun y ↦ by simp [Pi.le_def, forall_and]

@[to_dual self]
/-
**Set.piecewise_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_mem_Icc {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ 
: forall i, α i} (h₁ : forall i in s, f₁ i in Icc (g₁ i) (g₂ i)) (h₂ : forall i 
∉ s, f₂ i in Icc (g₁ i) (g₂ i)) : s.piecewise f₁ f₂ in Icc g₁ g₂
参数：j in s；h₁ : forall i in s, f₁ i in Icc (g₁ i) (g₂ i)；h₂ : forall i ∉ s, f₂ i 
in Icc (g₁ i) (g₂ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_piecewise`：le_piecewise {δ : α -> Type*} [forall i, Preorder (δ i
)] {s : Set α} [forall j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : fo
rall i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.piecewise_le`：piecewise_le {δ : α -> Type*} [forall i, Preorder (δ i
)] {s : Set α} [forall j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : fo
rall i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem piecewise_mem_Icc {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : ∀ i ∈ s, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ i ∉ s, f₂ i ∈ Icc (g₁ i) (g₂ i)) :
    s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  ⟨le_piecewise (fun i hi ↦ (h₁ i hi).1) fun i hi ↦ (h₂ i hi).1,
    piecewise_le (fun i hi ↦ (h₁ i hi).2) fun i hi ↦ (h₂ i hi).2⟩

@[to_dual self]
/-
**Set.piecewise_mem_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_mem_Icc' {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂
 : forall i, α i} (h₁ : f₁ in Icc g₁ g₂) (h₂ : f₂ in Icc g₁ g₂) : s.piecewise f₁
 f₂ in Icc g₁ g₂
参数：j in s；h₁ : f₁ in Icc g₁ g₂；h₂ : f₂ in Icc g₁ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_mem_Icc`：piecewise_mem_Icc {s : Set ι} [forall j, Decidabl
e (j in s)] {f₁ f₂ g₁ g₂ : forall i, α i} (h₁ : forall i in s, f₁ i in Icc (g₁ i
) (g₂ i)) (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem piecewise_mem_Icc' {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : f₁ ∈ Icc g₁ g₂) (h₂ : f₂ ∈ Icc g₁ g₂) : s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  piecewise_mem_Icc (fun _ _ ↦ ⟨h₁.1 _, h₁.2 _⟩) fun _ _ ↦ ⟨h₂.1 _, h₂.2 _⟩

section Nonempty

@[to_dual]
/-
**Set.pi_univ_Ioi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioi_subset [Nonempty ι] : (pi univ fun i => Ioi (x i)) subseteq Io
i x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `trivial`：True
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem pi_univ_Ioi_subset [Nonempty ι] : (pi univ fun i ↦ Ioi (x i)) ⊆ Ioi x := fun _ hz ↦
  ⟨fun i ↦ le_of_lt <| hz i trivial, fun h ↦
    (‹Nonempty ι›.elim) fun i ↦ not_lt_of_ge (h i) (hz i trivial)⟩

@[to_dual self]
/-
**Set.pi_univ_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioo_subset [Nonempty ι] : (pi univ fun i => Ioo (x i) (y i)) subse
teq Ioo x y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_univ_Ioi_subset`：pi_univ_Ioi_subset [Nonempty ι] : (pi univ fun i
 => Ioi (x i)) subseteq Ioi x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.pi_univ_Iio_subset`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i :
 ι) → Preorder (α i)] (x : (i : ι) → α i) [Nonempty ι],   (Set.univ.pi fun i => 
Set.Iio (x i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pi_univ_Ioo_subset [Nonempty ι] : (pi univ fun i ↦ Ioo (x i) (y i)) ⊆ Ioo x y := fun _ hx ↦
  ⟨(pi_univ_Ioi_subset _) fun i hi ↦ (hx i hi).1, (pi_univ_Iio_subset _) fun i hi ↦ (hx i hi).2⟩

@[to_dual]
/-
**Set.pi_univ_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioc_subset [Nonempty ι] : (pi univ fun i => Ioc (x i) (y i)) subse
teq Ioc x y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_univ_Ioi_subset`：pi_univ_Ioi_subset [Nonempty ι] : (pi univ fun i
 => Ioi (x i)) subseteq Ioi x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `trivial`：True
-/
theorem pi_univ_Ioc_subset [Nonempty ι] : (pi univ fun i ↦ Ioc (x i) (y i)) ⊆ Ioc x y := fun _ hx ↦
  ⟨(pi_univ_Ioi_subset _) fun i hi ↦ (hx i hi).1, fun i ↦ (hx i trivial).2⟩

end Nonempty

variable [DecidableEq ι]

open Function (update)

/-
**Set.pi_univ_Ioc_update_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioc_update_left {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : x 
i₀ <= m) : (pi univ fun i => Ioc (update x i₀ m i) (y i)) = { z | m < z i₀ } int
er pi univ fun i => Ioc (x i) (y i)
参数：hm : x i₀ <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_pi_update`：univ_pi_update [DecidableEq ι] {β : ι -> Type*} (i :
 ι) (f : forall j, α j) (a : α i) (t : forall j, α j -> Set (β j)) : (pi univ fu
n j => t…
· 使用定理 `Set.pi_inter_compl`：pi_inter_compl (s : Set ι) : pi s t inter pi sᶜ t = 
pi univ t
· 使用定理 `Set.singleton_pi'`：singleton_pi' (i : ι) (t : forall i, Set (α i)) : pi 
{i} t = { x | x i in t i }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem pi_univ_Ioc_update_left {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
    (pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) =
      { z | m < z i₀ } ∩ pi univ fun i ↦ Ioc (x i) (y i) := by
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z ↦ Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
/-
**Set.pi_univ_Ioc_update_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioc_update_right {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : m
 <= y i₀) : (pi univ fun i => Ioc (x i) (update y i₀ m i)) = { z | z i₀ <= m } i
nter pi univ fun i => Ioc (x i) (y i)
参数：hm : m <= y i₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `Set.inter_left_comm`：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ i
nter s₃) = s₂ inter (s₁ inter s₃)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_pi_update`：univ_pi_update [DecidableEq ι] {β : ι -> Type*} (i :
 ι) (f : forall j, α j) (a : α i) (t : forall j, α j -> Set (β j)) : (pi univ fu
n j => t…
· 使用定理 `Set.pi_inter_compl`：pi_inter_compl (s : Set ι) : pi s t inter pi sᶜ t = 
pi univ t
· 使用定理 `Set.singleton_pi'`：singleton_pi' (i : ι) (t : forall i, Set (α i)) : pi 
{i} t = { x | x i in t i }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem pi_univ_Ioc_update_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
    (pi univ fun i ↦ Ioc (x i) (update y i₀ m i)) =
      { z | z i₀ ≤ m } ∩ pi univ fun i ↦ Ioc (x i) (y i) := by
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm,
      inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z ↦ Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
/-
**Set.disjoint_pi_univ_Ioc_update_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_pi_univ_Ioc_update_left_right {x y : forall i, α i} {i₀ : ι} {m :
 α i₀} : Disjoint (pi univ fun i => Ioc (x i) (update y i₀ m i)) (pi univ fun i 
=> Ioc (update x i₀ m i) (y i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem disjoint_pi_univ_Ioc_update_left_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} :
    Disjoint (pi univ fun i ↦ Ioc (x i) (update y i₀ m i))
    (pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) := by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine (h₁ i₀ (mem_univ _)).2.not_gt ?_
  simpa only [Function.update_self] using (h₂ i₀ (mem_univ _)).1

end PiPreorder

section PiPartialOrder

variable [DecidableEq ι] [∀ i, PartialOrder (α i)]

-- Porting note: Dot notation on `Function.update` broke
/-
**Set.image_update_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Icc (f : forall i, α i) (i : ι) (a b : α i) : update f i '' I
cc a b = Icc (update f i a) (update f i b)
参数：f : forall i, α i；i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem image_update_Icc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Icc a b = Icc (update f i a) (update f i b) := by
  ext x
  rw [← Set.pi_univ_Icc]
  refine ⟨?_, fun h => ⟨x i, ?_, ?_⟩⟩
  · rintro ⟨c, hc, rfl⟩
    simpa [update_le_update_iff]
  · simpa only [Function.update_self] using! h i (mem_univ i)
  · ext j
    obtain rfl | hij := eq_or_ne i j
    · exact Function.update_self ..
    · simpa only [Function.update_of_ne hij.symm, le_antisymm_iff] using! h j (mem_univ j)
/-
**Set.image_update_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ico (f : forall i, α i) (i : ι) (a b : α i) : update f i '' I
co a b = Ico (update f i a) (update f i b)
参数：f : forall i, α i；i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
-/
theorem image_update_Ico (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ico a b = Ico (update f i a) (update f i b) := by
  rw [← Icc_sdiff_right, ← Icc_sdiff_right, image_sdiff (update_injective _ _), image_singleton,
    image_update_Icc]
/-
**Set.image_update_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioc (f : forall i, α i) (i : ι) (a b : α i) : update f i '' I
oc a b = Ioc (update f i a) (update f i b)
参数：f : forall i, α i；i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
-/
theorem image_update_Ioc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ioc a b = Ioc (update f i a) (update f i b) := by
  rw [← Icc_sdiff_left, ← Icc_sdiff_left, image_sdiff (update_injective _ _), image_singleton,
    image_update_Icc]
/-
**Set.image_update_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioo (f : forall i, α i) (i : ι) (a b : α i) : update f i '' I
oo a b = Ioo (update f i a) (update f i b)
参数：f : forall i, α i；i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.image_update_Ico`：image_update_Ico (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ico a b = Ico (update f i a) (update f i b)
-/
theorem image_update_Ioo (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ioo a b = Ioo (update f i a) (update f i b) := by
  rw [← Ico_sdiff_left, ← Ico_sdiff_left, image_sdiff (update_injective _ _), image_singleton,
    image_update_Ico]
/-
**Set.image_update_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Icc_left (f : forall i, α i) (i : ι) (a : α i) : update f i '
' Icc a (f i) = Icc (update f i a) f
参数：f : forall i, α i；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
-/
theorem image_update_Icc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Icc a (f i) = Icc (update f i a) f := by simpa using image_update_Icc f i a (f i)
/-
**Set.image_update_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ico_left (f : forall i, α i) (i : ι) (a : α i) : update f i '
' Ico a (f i) = Ico (update f i a) f
参数：f : forall i, α i；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ico`：image_update_Ico (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ico a b = Ico (update f i a) (update f i b)
-/
theorem image_update_Ico_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ico a (f i) = Ico (update f i a) f := by simpa using image_update_Ico f i a (f i)
/-
**Set.image_update_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioc_left (f : forall i, α i) (i : ι) (a : α i) : update f i '
' Ioc a (f i) = Ioc (update f i a) f
参数：f : forall i, α i；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ioc`：image_update_Ioc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioc a b = Ioc (update f i a) (update f i b)
-/
theorem image_update_Ioc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ioc a (f i) = Ioc (update f i a) f := by simpa using image_update_Ioc f i a (f i)
/-
**Set.image_update_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioo_left (f : forall i, α i) (i : ι) (a : α i) : update f i '
' Ioo a (f i) = Ioo (update f i a) f
参数：f : forall i, α i；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ioo`：image_update_Ioo (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioo a b = Ioo (update f i a) (update f i b)
-/
theorem image_update_Ioo_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ioo a (f i) = Ioo (update f i a) f := by simpa using image_update_Ioo f i a (f i)
/-
**Set.image_update_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Icc_right (f : forall i, α i) (i : ι) (b : α i) : update f i 
'' Icc (f i) b = Icc f (update f i b)
参数：f : forall i, α i；i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
-/
theorem image_update_Icc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Icc (f i) b = Icc f (update f i b) := by simpa using image_update_Icc f i (f i) b
/-
**Set.image_update_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ico_right (f : forall i, α i) (i : ι) (b : α i) : update f i 
'' Ico (f i) b = Ico f (update f i b)
参数：f : forall i, α i；i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ico`：image_update_Ico (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ico a b = Ico (update f i a) (update f i b)
-/
theorem image_update_Ico_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ico (f i) b = Ico f (update f i b) := by simpa using image_update_Ico f i (f i) b
/-
**Set.image_update_Ioc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioc_right (f : forall i, α i) (i : ι) (b : α i) : update f i 
'' Ioc (f i) b = Ioc f (update f i b)
参数：f : forall i, α i；i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ioc`：image_update_Ioc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioc a b = Ioc (update f i a) (update f i b)
-/
theorem image_update_Ioc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ioc (f i) b = Ioc f (update f i b) := by simpa using image_update_Ioc f i (f i) b
/-
**Set.image_update_Ioo_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_Ioo_right (f : forall i, α i) (i : ι) (b : α i) : update f i 
'' Ioo (f i) b = Ioo f (update f i b)
参数：f : forall i, α i；i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_Ioo`：image_update_Ioo (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioo a b = Ioo (update f i a) (update f i b)
-/
theorem image_update_Ioo_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ioo (f i) b = Ioo f (update f i b) := by simpa using image_update_Ioo f i (f i) b

variable [∀ i, One (α i)]

@[to_additive]
/-
**Set.image_mulSingle_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Icc (i : ι) (a b : α i) : Pi.mulSingle i '' Icc a b = Icc 
(Pi.mulSingle i a) (Pi.mulSingle i b)
参数：i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
-/
theorem image_mulSingle_Icc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Icc a b = Icc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Icc _ _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ico (i : ι) (a b : α i) : Pi.mulSingle i '' Ico a b = Ico 
(Pi.mulSingle i a) (Pi.mulSingle i b)
参数：i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ico`：image_update_Ico (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ico a b = Ico (update f i a) (update f i b)
-/
theorem image_mulSingle_Ico (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ico a b = Ico (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ico _ _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioc (i : ι) (a b : α i) : Pi.mulSingle i '' Ioc a b = Ioc 
(Pi.mulSingle i a) (Pi.mulSingle i b)
参数：i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioc`：image_update_Ioc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioc a b = Ioc (update f i a) (update f i b)
-/
theorem image_mulSingle_Ioc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioc a b = Ioc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioc _ _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioo (i : ι) (a b : α i) : Pi.mulSingle i '' Ioo a b = Ioo 
(Pi.mulSingle i a) (Pi.mulSingle i b)
参数：i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioo`：image_update_Ioo (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Ioo a b = Ioo (update f i a) (update f i b)
-/
theorem image_mulSingle_Ioo (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioo a b = Ioo (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioo _ _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Icc_left (i : ι) (a : α i) : Pi.mulSingle i '' Icc a 1 = I
cc (Pi.mulSingle i a) 1
参数：i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Icc_left`：image_update_Icc_left (f : forall i, α i) (i 
: ι) (a : α i) : update f i '' Icc a (f i) = Icc (update f i a) f
-/
theorem image_mulSingle_Icc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Icc a 1 = Icc (Pi.mulSingle i a) 1 :=
  image_update_Icc_left _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ico_left (i : ι) (a : α i) : Pi.mulSingle i '' Ico a 1 = I
co (Pi.mulSingle i a) 1
参数：i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ico_left`：image_update_Ico_left (f : forall i, α i) (i 
: ι) (a : α i) : update f i '' Ico a (f i) = Ico (update f i a) f
-/
theorem image_mulSingle_Ico_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ico a 1 = Ico (Pi.mulSingle i a) 1 :=
  image_update_Ico_left _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioc_left (i : ι) (a : α i) : Pi.mulSingle i '' Ioc a 1 = I
oc (Pi.mulSingle i a) 1
参数：i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioc_left`：image_update_Ioc_left (f : forall i, α i) (i 
: ι) (a : α i) : update f i '' Ioc a (f i) = Ioc (update f i a) f
-/
theorem image_mulSingle_Ioc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioc a 1 = Ioc (Pi.mulSingle i a) 1 :=
  image_update_Ioc_left _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioo_left (i : ι) (a : α i) : Pi.mulSingle i '' Ioo a 1 = I
oo (Pi.mulSingle i a) 1
参数：i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioo_left`：image_update_Ioo_left (f : forall i, α i) (i 
: ι) (a : α i) : update f i '' Ioo a (f i) = Ioo (update f i a) f
-/
theorem image_mulSingle_Ioo_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioo a 1 = Ioo (Pi.mulSingle i a) 1 :=
  image_update_Ioo_left _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Icc_right (i : ι) (b : α i) : Pi.mulSingle i '' Icc 1 b = 
Icc 1 (Pi.mulSingle i b)
参数：i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Icc_right`：image_update_Icc_right (f : forall i, α i) (
i : ι) (b : α i) : update f i '' Icc (f i) b = Icc f (update f i b)
-/
theorem image_mulSingle_Icc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Icc 1 b = Icc 1 (Pi.mulSingle i b) :=
  image_update_Icc_right _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ico_right (i : ι) (b : α i) : Pi.mulSingle i '' Ico 1 b = 
Ico 1 (Pi.mulSingle i b)
参数：i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ico_right`：image_update_Ico_right (f : forall i, α i) (
i : ι) (b : α i) : update f i '' Ico (f i) b = Ico f (update f i b)
-/
theorem image_mulSingle_Ico_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ico 1 b = Ico 1 (Pi.mulSingle i b) :=
  image_update_Ico_right _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioc_right (i : ι) (b : α i) : Pi.mulSingle i '' Ioc 1 b = 
Ioc 1 (Pi.mulSingle i b)
参数：i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioc_right`：image_update_Ioc_right (f : forall i, α i) (
i : ι) (b : α i) : update f i '' Ioc (f i) b = Ioc f (update f i b)
-/
theorem image_mulSingle_Ioc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioc 1 b = Ioc 1 (Pi.mulSingle i b) :=
  image_update_Ioc_right _ _ _

@[to_additive]
/-
**Set.image_mulSingle_Ioo_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_Ioo_right (i : ι) (b : α i) : Pi.mulSingle i '' Ioo 1 b = 
Ioo 1 (Pi.mulSingle i b)
参数：i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_Ioo_right`：image_update_Ioo_right (f : forall i, α i) (
i : ι) (b : α i) : update f i '' Ioo (f i) b = Ioo f (update f i b)
-/
theorem image_mulSingle_Ioo_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioo 1 b = Ioo 1 (Pi.mulSingle i b) :=
  image_update_Ioo_right _ _ _

end PiPartialOrder

section PiLattice

variable [∀ i, Lattice (α i)]

@[simp]
/-
**Set.pi_univ_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_uIcc (a b : forall i, α i) : (pi univ fun i => uIcc (a i) (b i)) =
 uIcc a b
参数：a b : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
-/
theorem pi_univ_uIcc (a b : ∀ i, α i) : (pi univ fun i => uIcc (a i) (b i)) = uIcc a b :=
  pi_univ_Icc _ _

variable [DecidableEq ι]
/-
**Set.image_update_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_uIcc (f : forall i, α i) (i : ι) (a b : α i) : update f i '' 
uIcc a b = uIcc (update f i a) (update f i b)
参数：f : forall i, α i；i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_update_Icc`：image_update_Icc (f : forall i, α i) (i : ι) (a b 
: α i) : update f i '' Icc a b = Icc (update f i a) (update f i b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_sup`：update_sup [forall i, SemilatticeSup (π i)] (f : fo
rall i, π i) (i : ι) (a b : π i) : update f i (a ⊔ b) = update f i a ⊔ update f 
i b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_inf`：∀ {ι : Type u_1} {π : ι → Type u_2} [inst : Decidab
leEq ι] [inst_1 : (i : ι) → SemilatticeInf (π i)] (f : (i : ι) → π i)   (i : ι) 
(a b : π …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_update_uIcc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' uIcc a b = uIcc (update f i a) (update f i b) :=
  (image_update_Icc _ _ _ _).trans <| by simp_rw [uIcc, update_sup, update_inf]
/-
**Set.image_update_uIcc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_uIcc_left (f : forall i, α i) (i : ι) (a : α i) : update f i 
'' uIcc a (f i) = uIcc (update f i a) f
参数：f : forall i, α i；i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_uIcc`：image_update_uIcc (f : forall i, α i) (i : ι) (a 
b : α i) : update f i '' uIcc a b = uIcc (update f i a) (update f i b)
-/
theorem image_update_uIcc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' uIcc a (f i) = uIcc (update f i a) f := by
  simpa using image_update_uIcc f i a (f i)
/-
**Set.image_update_uIcc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_update_uIcc_right (f : forall i, α i) (i : ι) (b : α i) : update f i
 '' uIcc (f i) b = uIcc f (update f i b)
参数：f : forall i, α i；i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.image_update_uIcc`：image_update_uIcc (f : forall i, α i) (i : ι) (a 
b : α i) : update f i '' uIcc a b = uIcc (update f i a) (update f i b)
-/
theorem image_update_uIcc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' uIcc (f i) b = uIcc f (update f i b) := by
  simpa using image_update_uIcc f i (f i) b

variable [∀ i, One (α i)]

@[to_additive]
/-
**Set.image_mulSingle_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_uIcc (i : ι) (a b : α i) : Pi.mulSingle i '' uIcc a b = uI
cc (Pi.mulSingle i a) (Pi.mulSingle i b)
参数：i : ι；a b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_uIcc`：image_update_uIcc (f : forall i, α i) (i : ι) (a 
b : α i) : update f i '' uIcc a b = uIcc (update f i a) (update f i b)
-/
theorem image_mulSingle_uIcc (i : ι) (a b : α i) :
    Pi.mulSingle i '' uIcc a b = uIcc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_uIcc _ _ _ _

@[to_additive]
/-
**Set.image_mulSingle_uIcc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_uIcc_left (i : ι) (a : α i) : Pi.mulSingle i '' uIcc a 1 =
 uIcc (Pi.mulSingle i a) 1
参数：i : ι；a : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_uIcc_left`：image_update_uIcc_left (f : forall i, α i) (
i : ι) (a : α i) : update f i '' uIcc a (f i) = uIcc (update f i a) f
-/
theorem image_mulSingle_uIcc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' uIcc a 1 = uIcc (Pi.mulSingle i a) 1 :=
  image_update_uIcc_left _ _ _

@[to_additive]
/-
**Set.image_mulSingle_uIcc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_mulSingle_uIcc_right (i : ι) (b : α i) : Pi.mulSingle i '' uIcc 1 b 
= uIcc 1 (Pi.mulSingle i b)
参数：i : ι；b : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_update_uIcc_right`：image_update_uIcc_right (f : forall i, α i)
 (i : ι) (b : α i) : update f i '' uIcc (f i) b = uIcc f (update f i b)
-/
theorem image_mulSingle_uIcc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' uIcc 1 b = uIcc 1 (Pi.mulSingle i b) :=
  image_update_uIcc_right _ _ _

end PiLattice

variable [DecidableEq ι] [∀ i, LinearOrder (α i)]

open Function (update)

/-
**Set.pi_univ_Ioc_update_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_Ioc_update_union (x y : forall i, α i) (i₀ : ι) (m : α i₀) (hm : m
 in Icc (x i₀) (y i₀)) : ((pi univ fun i => Ioc (x i) (update y i₀ m i)) union p
i univ fun i => Ioc (update x i₀ m i) (y i)) = pi univ fun i => Ioc (x i) (y i)
参数：x y : forall i, α i；i₀ : ι；m : α i₀；hm : m in Icc (x i₀) (y i₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_univ_Ioc_update_left`：pi_univ_Ioc_update_left {x y : forall i, α 
i} {i₀ : ι} {m : α i₀} (hm : x i₀ <= m) : (pi univ fun i => Ioc (update x i₀ m i
) (y i)) = { z | …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.pi_univ_Ioc_update_right`：pi_univ_Ioc_update_right {x y : forall i, 
α i} {i₀ : ι} {m : α i₀} (hm : m <= y i₀) : (pi univ fun i => Ioc (x i) (update 
y i₀ m i)) = { z |…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_univ_Ioc_update_union (x y : ∀ i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
    ((pi univ fun i ↦ Ioc (x i) (update y i₀ m i)) ∪
        pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) =
      pi univ fun i ↦ Ioc (x i) (y i) := by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← ofPred_or, le_or_gt, ofPred_true, univ_inter]

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
/-
**Set.Icc_sdiff_pi_univ_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_pi_univ_Ioo_subset (x y x' y' : forall i, α i) : (Icc x y \ pi u
niv fun i => Ioo (x' i) (y' i)) subseteq (⋃ i : ι, Icc x (update y i (x' i))) un
ion ⋃ i : ι, Icc (update x i (y' i)) y
参数：x y x' y' : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open interval
s `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference betwe
en a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered 
by the union
of the faces of `[x, y]`.
-/
theorem Icc_sdiff_pi_univ_Ioo_subset (x y x' y' : ∀ i, α i) :
    (Icc x y \ pi univ fun i ↦ Ioo (x' i) (y' i)) ⊆
    (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y := by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp only [mem_pi, mem_univ, mem_Ioo, true_implies, not_forall] at ha'
  simp only [le_update_iff, update_le_iff, mem_union, mem_iUnion, mem_Icc,
    hxa, hay _, hxa _, hay, ← exists_or]
  rcases ha' with ⟨w, hw⟩
  apply Exists.intro w
  cases lt_or_ge (x' w) (a w) <;> simp_all

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioo_subset := Icc_sdiff_pi_univ_Ioo_subset

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
/-
**Set.Icc_sdiff_pi_univ_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_pi_univ_Ioc_subset (x y z : forall i, α i) : (Icc x z \ pi univ 
fun i => Ioc (y i) (z i)) subseteq ⋃ i : ι, Icc x (update z i (y i))
参数：x y z : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y
 i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed bo
x
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is 
covered by the union
of the faces of `[x, y]` adjacent to `x`.
-/
theorem Icc_sdiff_pi_univ_Ioc_subset (x y z : ∀ i, α i) :
    (Icc x z \ pi univ fun i ↦ Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) := by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioc_subset := Icc_sdiff_pi_univ_Ioc_subset

end Set

