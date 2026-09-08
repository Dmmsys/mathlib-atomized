/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Control.Fix
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `Fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `Fix` instances in
`Control.Fix` are provided.

## Main definition

* class `LawfulFix`
-/

@[expose] public section

universe u v

variable {α : Type*} {β : α → Type*}

open OmegaCompletePartialOrder

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `Continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
/-
**LawfulFix** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [OmegaCompletePartialOrder α] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (
fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence
 of "exotic"
functions `f`, such as the function that is defined iff its argument is not, fam
iliar from the
halting problem. Instead, this requirement is limited to only functions that are
 `Continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is n
ot monotone
(making the input argument less defined can make `f` more defined).
-/
class LawfulFix (α : Type*) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : ∀ {f : α → α}, ωScottContinuous f → Fix.fix f = f (Fix.fix f)

namespace Part

open Nat Nat.Upto

namespace Fix

variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

/-
**Part.Fix.approx_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：approx_mono' {i : Nat} : Fix.approx f i <= Fix.approx f (succ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem approx_mono' {i : ℕ} : Fix.approx f i ≤ Fix.approx f (succ i) := by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih
/-
**Part.Fix.approx_mono** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：approx_mono ⦃i j : Nat⦄ (hij : i <= j) : approx f i <= approx f j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Part.Fix.approx_mono'`：approx_mono' {i : Nat} : Fix.approx f i <= Fix.ap
prox f (succ i)
-/
theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j := by
  induction j with
  | zero => cases hij; exact le_rfl
  | succ j ih =>
    cases hij; · exact le_rfl
    exact le_trans (ih ‹_›) (approx_mono' f)
/-
**Part.Fix.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：mem_iff (a : α) (b : β a) : b in Part.fix f a ↔ exists i, b in approx f i 
a
参数：a : α；b : β a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.fix_def`：∀ {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → Part (
β a)) → (a : α) → Part (β a)) {x : α}   (h' : ∃ i, (Part.Fix.approx f i x).Dom),
 P…
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
· 使用定理 `Part.Fix.approx_mono'`：approx_mono' {i : Nat} : Fix.approx f i <= Fix.ap
prox f (succ i)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Part.Fix.approx_mono`：approx_mono ⦃i j : Nat⦄ (hij : i <= j) : approx f 
i <= approx f j
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Part.fix_def'`：fix_def' {x : α} (h' : ¬exists i, (Fix.approx f i x).Dom)
 : Part.fix f x = none
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem mem_iff (a : α) (b : β a) : b ∈ Part.fix f a ↔ ∃ i, b ∈ approx f i a := by
  classical
  by_cases h₀ : ∃ i : ℕ, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    obtain ⟨y, h₁⟩ := h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
      subst this
      exact h₁
    obtain ⟨i, hh⟩ := hh
    revert h₁; generalize succ (Nat.find h₀) = j; intro h₁
    wlog case : i ≤ j
    · rcases le_total i j with H | H <;> [skip; symm] <;> apply_assumption <;> assumption
    replace hh := approx_mono f case _ _ hh
    apply Part.mem_unique h₁ hh
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff, notMem_none]
    simp only [dom_iff_mem, not_exists] at h₀
    intro; apply h₀
/-
**Part.Fix.approx_le_fix** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：approx_le_fix (i : Nat) : approx f i <= Part.fix f
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.Fix.mem_iff`：mem_iff (a : α) (b : β a) : b in Part.fix f a ↔ exists
 i, b in approx f i a
-/
theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f := fun a b hh ↦ by
  rw [mem_iff f]
  exact ⟨_, hh⟩
/-
**Part.Fix.exists_fix_le_approx** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：exists_fix_le_approx (x : α) : exists i, Part.fix f x <= approx f i x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.Fix.approx_le_fix`：approx_le_fix (i : Nat) : approx f i <= Part.fix
 f
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `Part.Fix.mem_iff`：mem_iff (a : α) (b : β a) : b in Part.fix f a ↔ exists
 i, b in approx f i a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem exists_fix_le_approx (x : α) : ∃ i, Part.fix f x ≤ approx f i x := by
  by_cases! hh : ∃ i b, b ∈ approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    obtain ⟨i, h'⟩ := h'
    cases hh _ _ h'

/-- The series of approximations of `fix f` (see `approx`) as a `Chain` -/
/-
**Part.Fix.approxChain** 是 Mathlib 中的一个定义，位于命名空间 `Part.Fix`。
形式化陈述：approxChain : Chain ((a : _) -> Part <| β a)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Part.Fix.approx_mono`：approx_mono ⦃i j : Nat⦄ (hij : i <= j) : approx f 
i <= approx f j

--- 原说明 ---
The series of approximations of `fix f` (see `approx`) as a `Chain`
-/
def approxChain : Chain ((a : _) → Part <| β a) :=
  ⟨approx f, approx_mono f⟩
/-
**Part.Fix.le_f_of_mem_approx** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：le_f_of_mem_approx {x} : x in approxChain f -> x <= f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.Fix.approx_mono'`：approx_mono' {i : Nat} : Fix.approx f i <= Fix.ap
prox f (succ i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_f_of_mem_approx {x} : x ∈ approxChain f → x ≤ f x := by
  simp only [Membership.mem, forall_exists_index]
  rintro i rfl
  apply approx_mono'
/-
**Part.Fix.approx_mem_approxChain** 是 Mathlib 中的一个定理，位于命名空间 `Part.Fix`。
形式化陈述：approx_mem_approxChain {i} : approx f i in approxChain f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.mem_of_get_eq`：mem_of_get_eq {n : Nat} {s : Stream' α} {a : α} :
 a = get s n -> a in s
-/
theorem approx_mem_approxChain {i} : approx f i ∈ approxChain f :=
  Stream'.mem_of_get_eq rfl

end Fix

open Part.Fix

variable {α : Type*}
variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

/-
**Part.fix_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fix_eq_ωSup : Part.fix f = ωSup (approxChain f) := by
  apply le_antisymm
  · intro x
    obtain ⟨i, hx⟩ := exists_fix_le_approx f x
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain]
    intro y x
    apply approx_le_fix f
/-
**Part.fix_le** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：fix_le {X : (a : _) -> Part <| β a} (hX : f X <= X) : Part.fix f <= X
参数：a : _；hX : f X <= X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.fix_eq_ωSup`：fix_eq_ωSup : Part.fix f = ωSup (approxChain f)
· 使用定理 `OmegaCompletePartialOrder.ωSup_le`：∀ {α : Type u_6} [self : OmegaComplet
ePartialOrder α] (c : OmegaCompletePartialOrder.Chain α) (x : α),   (∀ (i : ℕ), 
c i ≤ x) → OmegaComplet…
· 使用定理 `Part.Fix.approx_mono`：approx_mono ⦃i j : Nat⦄ (hij : i <= j) : approx f 
i <= approx f j
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem fix_le {X : (a : _) → Part <| β a} (hX : f X ≤ X) : Part.fix f ≤ X := by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain]
  intro i
  induction i with
  | zero => apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

variable {g : ((a : _) → Part <| β a) → (a : _) → Part <| β a}
/-
**Part.fix_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fix_eq_ωSup_of_ωScottContinuous (hc : ωScottContinuous g) : Part.fix g =
    ωSup (approxChain (⟨g,hc.monotone⟩ : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)) := by
  rw [← fix_eq_ωSup]
  rfl
/-
**Part.fix_eq_of_** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fix_eq_of_ωScottContinuous (hc : ωScottContinuous g) :
    Part.fix g = g (Part.fix g) := by
  rw [fix_eq_ωSup_of_ωScottContinuous hc, hc.map_ωSup]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ

end Part

namespace Part

/-- `toUnit` as a monotone function -/
@[simps]
/-
**Part.toUnitMono** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：toUnitMono (f : Part α ->o Part α) : (Unit -> Part α) ->o Unit -> Part α w
here toFun x u
参数：f : Part α ->o Part α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toUnit` as a monotone function
-/
def toUnitMono (f : Part α →o Part α) : (Unit → Part α) →o Unit → Part α where
  toFun x u := f (x u)
  monotone' x y (h : x ≤ y) u := f.monotone <| h u

set_option backward.defeqAttrib.useBackward true in
/-
**Part.** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωScottContinuous_toUnitMono (f : Part α → Part α) (hc : ωScottContinuous f) :
    ωScottContinuous (toUnitMono ⟨f,hc.monotone⟩) := .of_map_ωSup_of_orderHom fun _ => by
  ext ⟨⟩ : 1
  dsimp [OmegaCompletePartialOrder.ωSup]
  erw [hc.map_ωSup]
  rw [Chain.map_comp]
  rfl
/-
**Part.lawfulFix** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
形式化陈述：lawfulFix : LawfulFix (Part α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance lawfulFix : LawfulFix (Part α) :=
  ⟨fun {f : Part α → Part α} hc ↦ show Part.fix (toUnitMono ⟨f,hc.monotone⟩) () = _ by
    rw [Part.fix_eq_of_ωScottContinuous (ωScottContinuous_toUnitMono f hc)]; rfl⟩

end Part

open Sigma

namespace Pi

/-
**Pi.lawfulFix** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：lawfulFix {β} : LawfulFix (α -> Part β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance lawfulFix {β} : LawfulFix (α → Part β) :=
  ⟨fun {_f} ↦ Part.fix_eq_of_ωScottContinuous⟩

variable {γ : ∀ a : α, β a → Type*}

section Monotone

variable (α β γ)

/-- `Sigma.curry` as a monotone function. -/
@[simps]
/-
**Pi.monotoneCurry** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：monotoneCurry [(x y : _) -> Preorder <| γ x y] : (forall x : Σ a, β a, γ x
.1 x.2) ->o forall (a) (b : β a), γ a b where toFun
参数：x y : _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sigma.curry` as a monotone function.
-/
def monotoneCurry [(x y : _) → Preorder <| γ x y] :
    (∀ x : Σ a, β a, γ x.1 x.2) →o ∀ (a) (b : β a), γ a b where
  toFun := curry
  monotone' _x _y h a b := h ⟨a, b⟩

/-- `Sigma.uncurry` as a monotone function. -/
@[simps]
/-
**Pi.monotoneUncurry** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：monotoneUncurry [(x y : _) -> Preorder <| γ x y] : (forall (a) (b : β a), 
γ a b) ->o forall x : Σ a, β a, γ x.1 x.2 where toFun
参数：x y : _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sigma.uncurry` as a monotone function.
-/
def monotoneUncurry [(x y : _) → Preorder <| γ x y] :
    (∀ (a) (b : β a), γ a b) →o ∀ x : Σ a, β a, γ x.1 x.2 where
  toFun := uncurry
  monotone' _x _y h a := h a.1 a.2

variable [(x y : _) → OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain
/-
**Pi.** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωScottContinuous_curry :
    ωScottContinuous (monotoneCurry α β γ) :=
  ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ by
    ext x y
    dsimp [curry, ωSup]
    rw [map_comp, map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
/-
**Pi.** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωScottContinuous_uncurry :
    ωScottContinuous (monotoneUncurry α β γ) :=
    .of_map_ωSup_of_orderHom fun c ↦ by
  ext ⟨x, y⟩
  dsimp [uncurry, ωSup]
  rw [map_comp, map_comp]
  rfl

end Monotone

open Fix

/-
**Pi.hasFix** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：hasFix [Fix <| (x : Sigma β) -> γ x.1 x.2] : Fix ((x : _) -> (y : β x) -> 
γ x y)
参数：x : Sigma β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasFix [Fix <| (x : Sigma β) → γ x.1 x.2] : Fix ((x : _) → (y : β x) → γ x y) :=
  ⟨fun f ↦ curry (fix <| uncurry ∘ f ∘ curry)⟩

variable [∀ x y, OmegaCompletePartialOrder <| γ x y]

section Curry

variable {f : (∀ a b, γ a b) → ∀ a b, γ a b}

/-
**Pi.uncurry_curry_** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_curry_ωScottContinuous (hc : ωScottContinuous f) :
    ωScottContinuous <| (monotoneUncurry α β γ).comp <|
      (⟨f,hc.monotone⟩ : ((x : _) → (y : β x) → γ x y) →o (x : _) → (y : β x) → γ x y).comp <|
      monotoneCurry α β γ :=
  (ωScottContinuous_uncurry _ _ _).comp (hc.comp (ωScottContinuous_curry _ _ _))

end Curry

/-
**Pi.lawfulFix'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：lawfulFix' [LawfulFix <| (x : Sigma β) -> γ x.1 x.2] : LawfulFix ((x y : _
) -> γ x y) where fix_eq {_f} hc
参数：x : Sigma β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lawfulFix' [LawfulFix <| (x : Sigma β) → γ x.1 x.2] :
    LawfulFix ((x y : _) → γ x y) where
  fix_eq {_f} hc := by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_ωScottContinuous hc)]
    rfl

end Pi

