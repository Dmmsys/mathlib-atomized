/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.ApplyFun

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `Perm α` and `derangements α`:
* `derangementsOptionEquivSigmaAtMostOneFixedPoint`: An equivalence between
  `derangements (Option α)` and the sigma-type `Σ a : α, {f : Perm α // fixedPoints f ⊆ a}`.
* `derangementsRecursionEquiv`: An equivalence between `derangements (Option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : Set α) : Type*) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `Equiv.removeNone`
on derangements: `RemoveNone.fiber_none` and `RemoveNone.fiber_some`.
-/

@[expose] public section


open Equiv Function

/-- A permutation is a derangement if it has no fixed points. -/
/-
**derangements** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：derangements (α : Type*) : Set (Perm α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A permutation is a derangement if it has no fixed points.
-/
def derangements (α : Type*) : Set (Perm α) :=
  { f : Perm α | ∀ x : α, f x ≠ x }

variable {α β : Type*}
/-
**mem_derangements_iff_fixedPoints_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_derangements_iff_fixedPoints_eq_empty {f : Perm α} : f in derangements
 α ↔ fixedPoints f = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
-/
theorem mem_derangements_iff_fixedPoints_eq_empty {f : Perm α} :
    f ∈ derangements α ↔ fixedPoints f = ∅ :=
  Set.eq_empty_iff_forall_notMem.symm

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
/-
**Equiv.derangementsCongr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.derangementsCongr (e : α ≃ β) : derangements α ≃ derangements β
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangement
s β`.
-/
def Equiv.derangementsCongr (e : α ≃ β) : derangements α ≃ derangements β :=
  e.permCongr.subtypeEquiv fun {f} => e.forall_congr <| by
    intro b; simp only [ne_eq, permCongr_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]

namespace derangements

set_option backward.isDefEq.respectTransparency false in
/-- Derangements on a subtype are equivalent to permutations on the original type where points are
fixed iff they are not in the subtype. -/
/-
**derangements.subtypeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `derangements`。
形式化陈述：{α : Type u_1} →   (p : α → Prop) →     [DecidablePred p] → ↑(derangements
 (Subtype p)) ≃ { f // ∀ (a : α), ¬p a ↔ a ∈ Function.fixedPoints ⇑f }
参数：p : α → Prop；derangements (Subtype p)；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derangements on a subtype are equivalent to permutations on the original type wh
ere points are
fixed iff they are not in the subtype.
-/
protected def subtypeEquiv (p : α → Prop) [DecidablePred p] :
    derangements (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
  calc
    derangements (Subtype p) ≃ { f : { f : Perm α // ∀ a, ¬p a → a ∈ fixedPoints f } //
        ∀ a, a ∈ fixedPoints f → ¬p a } := by
      refine (Perm.subtypeEquivSubtypePerm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => ?_, ?_⟩
      · refine hf ⟨a, ha⟩ (Subtype.ext ?_)
        simp_rw [mem_fixedPoints, IsFixedPt, Perm.subtypeEquivSubtypePerm,
        Equiv.coe_fn_mk, Perm.ofSubtype_apply_of_mem _ ha] at hfa
        assumption
      rintro hf ⟨a, ha⟩ hfa
      refine hf _ ?_ ha
      simp only [Perm.subtypeEquivSubtypePerm_apply_coe, mem_fixedPoints]
      dsimp [IsFixedPt]
      simp_rw [Perm.ofSubtype_apply_of_mem _ ha, hfa]
    _ ≃ { f : Perm α // ∃ _h : ∀ a, ¬p a → a ∈ fixedPoints f, ∀ a, a ∈ fixedPoints f → ¬p a } :=
      subtypeSubtypeEquivSubtypeExists _ _
    _ ≃ { f : Perm α // ∀ a, ¬p a ↔ a ∈ fixedPoints f } :=
      subtypeEquivRight fun f => by
        simp_rw [exists_prop, ← forall_and, ← iff_iff_implies_and_implies]

universe u
/-- The set of permutations that fix either `a` or nothing is equivalent to the sum of:
- derangements on `α`
- derangements on `α` minus `a`. -/
/-
**derangements.atMostOneFixedPointEquivSum_derangements** 是 Mathlib 中的一个定义，位于命名空
间 `derangements`。
形式化陈述：atMostOneFixedPointEquivSum_derangements [DecidableEq α] (a : α) : { f : P
erm α // fixedPoints f subseteq {a} } ≃ (derangements ({a}ᶜ : Set α)) oplus (der
angements α)
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The set of permutations that fix either `a` or nothing is equivalent to the sum 
of:
- derangements on `α`
- derangements on `α` minus `a`.
-/
def atMostOneFixedPointEquivSum_derangements [DecidableEq α] (a : α) :
    { f : Perm α // fixedPoints f ⊆ {a} } ≃ (derangements ({a}ᶜ : Set α)) ⊕ (derangements α) :=
  calc
    { f : Perm α // fixedPoints f ⊆ {a} } ≃
        { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∈ fixedPoints f } ⊕
          { f : { f : Perm α // fixedPoints f ⊆ {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃ { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∈ fixedPoints f } ⊕
          { f : Perm α // fixedPoints f ⊆ {a} ∧ a ∉ fixedPoints f } := by
      refine Equiv.sumCongr ?_ ?_
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x ⊆ {a})
          (a ∈ fixedPoints ·)
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x ⊆ {a})
          (a ∉ fixedPoints ·)
    _ ≃ { f : Perm α // fixedPoints f = {a} } ⊕ { f : Perm α // fixedPoints f = ∅ } := by
      refine Equiv.sumCongr (subtypeEquivRight fun f => ?_) (subtypeEquivRight fun f => ?_)
      · rw [Set.eq_singleton_iff_unique_mem, and_comm]
        rfl
      · rw [Set.eq_empty_iff_forall_notMem]
        exact ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
    _ ≃ derangements ({a}ᶜ : Set α) ⊕ derangements α := by
      refine
        Equiv.sumCongr ((derangements.subtypeEquiv _).trans <|
            subtypeEquivRight fun x => ?_).symm
          (subtypeEquivRight fun f => mem_derangements_iff_fixedPoints_eq_empty.symm)
      rw [eq_comm, Set.ext_iff]
      simp_rw [Set.mem_compl_iff, Classical.not_not]

namespace Equiv

variable [DecidableEq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
`Equiv.Perm.decomposeOption` is a derangement. -/
/-
**derangements.Equiv.RemoveNone.fiber** 是 Mathlib 中的一个定义，位于命名空间 `derangements.Eq
uiv.RemoveNone`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → Option α → Set (Equiv.Perm α)
参数：Equiv.Perm α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of permutations `f` such that the preimage of `(a, f)` under
`Equiv.Perm.decomposeOption` is a derangement.
-/
def RemoveNone.fiber (a : Option α) : Set (Perm α) :=
  { f : Perm α | (a, f) ∈ Equiv.Perm.decomposeOption '' derangements (Option α) }

set_option backward.isDefEq.respectTransparency false in
/-
**derangements.Equiv.RemoveNone.mem_fiber** 是 Mathlib 中的一个定理，位于命名空间 `derangement
s.Equiv.RemoveNone`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : Option α) (f : Equiv.Perm α),
   f ∈ derangements.Equiv.RemoveNone.fiber a ↔ ∃ F ∈ derangements (Option α), F 
none = a ∧ Equiv.removeNone F = f
参数：a : Option α；f : Equiv.Perm α；Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.Perm.decomposeOption_apply`：∀ {α : Type u_1} [inst : DecidableEq α
] (σ : Equiv.Perm (Option α)),   Equiv.Perm.decomposeOption σ = (σ none, Equiv.r
emoveNone σ)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem RemoveNone.mem_fiber (a : Option α) (f : Perm α) :
    f ∈ RemoveNone.fiber a ↔
      ∃ F : Perm (Option α), F ∈ derangements (Option α) ∧ F none = a ∧ removeNone F = f := by
  simp [RemoveNone.fiber, derangements]
/-
**derangements.Equiv.RemoveNone.fiber_none** 是 Mathlib 中的一个定理，位于命名空间 `derangemen
ts.Equiv.RemoveNone`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α], derangements.Equiv.RemoveNone.fib
er none = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `derangements.Equiv.RemoveNone.mem_fiber`：∀ {α : Type u_1} [inst : Decida
bleEq α] (a : Option α) (f : Equiv.Perm α),   f ∈ derangements.Equiv.RemoveNone.
fiber a ↔ ∃ F ∈ derangements …
-/
theorem RemoveNone.fiber_none : RemoveNone.fiber (@none α) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro f hyp
  rw [RemoveNone.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none

/-- For any `a : α`, the fiber over `some a` is the set of permutations
where `a` is the only possible fixed point. -/
/-
**derangements.Equiv.RemoveNone.fiber_some** 是 Mathlib 中的一个定理，位于命名空间 `derangemen
ts.Equiv.RemoveNone`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α),   derangements.Equiv.Remo
veNone.fiber (some a) = {f | Function.fixedPoints ⇑f ⊆ {a}}
参数：a : α；some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derangements.Equiv.RemoveNone.mem_fiber`：∀ {α : Type u_1} [inst : Decida
bleEq α] (a : Option α) (f : Equiv.Perm α),   f ∈ derangements.Equiv.RemoveNone.
fiber a ↔ ∃ F ∈ derangements …
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `Equiv.removeNone_none`：removeNone_none {x : α} (h : e (some x) = none) :
 some (removeNone e x) = e none
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Equiv.removeNone_some`：removeNone_some {x : α} (h : exists x', e (some x
) = some x') : some (removeNone e x) = e (some x)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.swap_apply_self`：swap_apply_self (i j a : α) : swap i j (swap i j 
a) = a
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
For any `a : α`, the fiber over `some a` is the set of permutations
where `a` is the only possible fixed point.
-/
theorem RemoveNone.fiber_some (a : α) :
    RemoveNone.fiber (some a) = { f : Perm α | fixedPoints f ⊆ {a} } := by
  ext f
  constructor
  · rw [RemoveNone.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixedPoints_iff] at x_fixed
    apply_fun some at x_fixed
    rcases Fx : F (some x) with - | y
    · rwa [removeNone_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    · exfalso
      rw [removeNone_some F ⟨y, Fx⟩] at x_fixed
      exact F_derangement _ x_fixed
  · intro h_opfp
    use Equiv.Perm.decomposeOption.symm (some a, f)
    constructor
    · intro x
      apply_fun fun x => Equiv.swap none (some a) x
      simp only [Perm.decomposeOption_symm_apply, Perm.coe_mul]
      rcases x with - | x
      · simp
      simp only [comp, optionCongr_apply, Option.map_some, swap_apply_self]
      by_cases x_vs_a : x = a
      · rw [x_vs_a, swap_apply_right]
        apply Option.some_ne_none
      have ne_1 : some x ≠ none := Option.some_ne_none _
      have ne_2 : some x ≠ some a := (Option.some_injective α).ne_iff.mpr x_vs_a
      rw [swap_apply_of_ne_of_ne ne_1 ne_2, (Option.some_injective α).ne_iff]
      intro contra
      exact x_vs_a (h_opfp contra)
    · rw [apply_symm_apply]

end Equiv

section Option

variable [DecidableEq α]

/-- The set of derangements on `Option α` is equivalent to the union over `a : α`
of "permutations with `a` the only possible fixed point". -/
/-
**derangements.derangementsOptionEquivSigmaAtMostOneFixedPoint** 是 Mathlib 中的一个定
义，位于命名空间 `derangements`。
形式化陈述：derangementsOptionEquivSigmaAtMostOneFixedPoint : derangements (Option α) 
≃ Σ a : α, { f : Perm α | fixedPoints f subseteq {a} }
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The set of derangements on `Option α` is equivalent to the union over `a : α`
of "permutations with `a` the only possible fixed point".
-/
def derangementsOptionEquivSigmaAtMostOneFixedPoint :
    derangements (Option α) ≃ Σ a : α, { f : Perm α | fixedPoints f ⊆ {a} } := by
  have fiber_none_is_false : Equiv.RemoveNone.fiber (@none α) → False := by
    rw [Equiv.RemoveNone.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σ a : Option α, ↥(Equiv.RemoveNone.fiber a) := setProdEquivSigma _
    _ ≃ Σ a : α, ↥(Equiv.RemoveNone.fiber (some a)) :=
      sigmaOptionEquivOfSome _ fiber_none_is_false
    _ ≃ Σ a : α, { f : Perm α | fixedPoints f ⊆ {a} } := by
      simp_rw [Equiv.RemoveNone.fiber_some]
      rfl

/-- The set of derangements on `Option α` is equivalent to the union over all `a : α` of
"derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
/-
**derangements.derangementsRecursionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `derangement
s`。
形式化陈述：derangementsRecursionEquiv : derangements (Option α) ≃ Σ a : α, derangemen
ts (({a}ᶜ : Set α) : Type _) oplus derangements α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The set of derangements on `Option α` is equivalent to the union over all `a : α
` of
"derangements on `α` ⊕ derangements on `{a}ᶜ`".
-/
def derangementsRecursionEquiv :
    derangements (Option α) ≃
      Σ a : α, derangements (({a}ᶜ : Set α) : Type _) ⊕ derangements α :=
  derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSum_derangements)

end Option

end derangements

