/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Joris van Winden
-/
module

public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Stochastic processes with independent increments

A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent.
Equivalently, for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)`
are independent.

## Main definition

* `HasIndepIncrements`: A stochastic process `X : T → Ω → E` has independent increments if for any
  `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are
  independent.

## Main statement

* `hasIndepIncrements_iff_nat`: A stochastic process `X : T → Ω → E` has independent increments if
  and only if for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)` are
  independent.

## Tags

independent increments
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  [Preorder T] [MeasurableSpace E]

section Def

variable [Sub E]

/-- A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent.

Although this corresponds to the standard definition, dealing with `Fin` might make things
complicated in some cases. Therefore we provide `HasIndepIncrements.of_nat` which instead requires
to prove that for any monotone sequence `(tₙ)` that is eventually constant,
the random variables `X tₙ₊₁ - X tₙ` are independent. -/
/-
**ProbabilityTheory.HasIndepIncrements** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：HasIndepIncrements (X : T -> Ω -> E) (P : Measure Ω
参数：X : T -> Ω -> E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 
1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are inde
pendent.

Although this corresponds to the standard definition, dealing with `Fin` might m
ake things
complicated in some cases. Therefore we provide `HasIndepIncrements.of_nat` whic
h instead requires
to prove that for any monotone sequence `(tₙ)` that is eventually constant,
the random variables `X tₙ₊₁ - X tₙ` are independent.
-/
def HasIndepIncrements (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P
/-
**ProbabilityTheory.HasIndepIncrements.nat** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] [inst_2 : Sub E],   ProbabilityTheory.HasIndepIncrements X P →   
  ∀ {t : ℕ → T}, Monotone t → ProbabilityTheory.iIndepFun (fun i ω => X (t (i + 
1)) ω - X (t i) ω) P
参数：fun i ω => X (t (i + 1)) ω - X (t i) ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ProbabilityTheory.iIndepFun_iff_finset`：iIndepFun_iff_finset : iIndepFun
 f μ ↔ forall s : Finset ι, iIndepFun (s.restrict f) μ where mp h s
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `ProbabilityTheory.iIndepFun.of_subsingleton`：∀ {Ω : Type u_1} {ι : Type 
u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [Subsingleton ι]   {β
 : ι → Type u_7} {m : (i : ι) → M…
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ProbabilityTheory.iIndepFun.precomp`：∀ {Ω : Type u_1} {ι : Type u_2} {x 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → ι} 
  {β : ι → Type u_7} {m :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Fin.val_strictMono`：val_strictMono : StrictMono (val : Fin n -> Nat)
-/
protected lemma HasIndepIncrements.nat
    (hX : HasIndepIncrements X P) {t : ℕ → T} (ht : Monotone t) :
    iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P := by
  refine iIndepFun_iff_finset.2 fun s ↦ ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · have := (hX 0 (fun _ ↦ t 0) (fun _ ↦ by grind)).isProbabilityMeasure
    exact iIndepFun.of_subsingleton
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    refine iIndepFun.precomp (g := g) ?_ (hX (s.max' hs + 1) (fun m ↦ t m) ?_)
    · simp [g, Function.Injective]
    · exact ht.comp Fin.val_strictMono.monotone
/-
**ProbabilityTheory.HasIndepIncrements.of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] [inst_2 : Sub E],   (∀ (t : ℕ → T),       Monotone t →         Fi
lter.EventuallyConst t Filter.atTop →           ProbabilityTheory.iIndepFun (fun
 i ω => X (t (i + 1)) ω - X (t i) ω) P) →     ProbabilityTheory.HasIndepIncremen
ts X P
参数：∀ (t : ℕ → T),       Monotone t →         Filter.EventuallyConst t Filter.atT
op →           ProbabilityTheory.iIndepFun (fun i ω => X (t (i + 1)) ω - X (t i)
 ω) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `ProbabilityTheory.iIndepFun.precomp`：∀ {Ω : Type u_1} {ι : Type u_2} {x 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → ι} 
  {β : ι → Type u_7} {m :…
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventuallyConst_atTop`：eventuallyConst_atTop [SemilatticeSup α] [
Nonempty α] : EventuallyConst f atTop ↔ (exists i, forall j, i <= j -> f j = f i
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
protected lemma HasIndepIncrements.of_nat
    (h : ∀ t : ℕ → T, Monotone t → EventuallyConst t atTop →
      iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert! (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · grind
  · grind
  · exact fun a b hab ↦ ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩
/-
**ProbabilityTheory.hasIndepIncrements_iff_nat** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：hasIndepIncrements_iff_nat : HasIndepIncrements X P ↔ forall t : Nat -> T,
 Monotone t -> iIndepFun (fun i ω => X (t (i + 1)) ω - X (t i) ω) P where mp h _
 ht
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasIndepIncrements.nat`：∀ {T : Type u_1} {Ω : Type u_2
} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : T →
 Ω → E}   [inst : Preorder T] …
· 使用定理 `ProbabilityTheory.HasIndepIncrements.of_nat`：∀ {T : Type u_1} {Ω : Type 
u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : 
T → Ω → E}   [inst : Preorder T] …
-/
lemma hasIndepIncrements_iff_nat :
    HasIndepIncrements X P ↔
    ∀ t : ℕ → T, Monotone t → iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P where
  mp h _ ht := h.nat ht
  mpr h := .of_nat (fun t ht _ ↦ h t ht)

end Def

/-
**ProbabilityTheory.HasIndepIncrements.indepFun_sub_sub** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] [inst_2 : Sub E],   ProbabilityTheory.HasIndepIncrements X P →   
  ∀ {r s t : T}, r ≤ s → s ≤ t → ProbabilityTheory.IndepFun (X s - X r) (X t - X
 s) P
参数：X s - X r；X t - X s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.indepFun`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_6}   {m : 
(x : ι) → MeasurableSpace …
· 使用定理 `ProbabilityTheory.HasIndepIncrements.nat`：∀ {T : Type u_1} {Ω : Type u_2
} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : T →
 Ω → E}   [inst : Preorder T] …
-/
lemma HasIndepIncrements.indepFun_sub_sub [Sub E] (hX : HasIndepIncrements X P) {r s t : T}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (X s - X r) ⟂ᵢ[P] (X t - X s) := by
  let τ : ℕ → T
    | 0 => r
    | 1 => s
    | _ => t
  exact hX.nat (t := τ) (fun _ ↦ by grind) |>.indepFun (by grind : 0 ≠ 1)
/-
**ProbabilityTheory.HasIndepIncrements.indepFun_eval_sub** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] [inst_2 : SubNegZeroMonoid E],   ProbabilityTheory.HasIndepIncrem
ents X P →     ∀ {r s t : T}, r ≤ s → s ≤ t → (∀ᵐ (ω : Ω) ∂P, X r ω = 0) → Proba
bilityTheory.IndepFun (X s) (X t - X s) P
参数：∀ᵐ (ω : Ω) ∂P, X r ω = 0；X s；X t - X s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IndepFun.congr`：∀ {Ω : Type u_1} {β : Type u_6} {β' : 
Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   
{g : Ω → β'} {mβ : Mea…
· 使用定理 `ProbabilityTheory.HasIndepIncrements.indepFun_sub_sub`：∀ {T : Type u_1} 
{Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measur
e Ω} {X : T → Ω → E}   [inst : Preorder T] …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma HasIndepIncrements.indepFun_eval_sub [SubNegZeroMonoid E] (hX : HasIndepIncrements X P)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) (h : ∀ᵐ ω ∂P, X r ω = 0) :
    (X s) ⟂ᵢ[P] (X t - X s) := by
  refine (hX.indepFun_sub_sub hrs hst).congr ?_ .rfl
  filter_upwards [h] with ω hω using by simp [hω]
/-
**ProbabilityTheory.HasIndepIncrements.map'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] {F : Type u_4} {G : Type u_5} [inst_2 : MeasurableSpace G]   [ins
t_3 : FunLike F E G] [inst_4 : AddGroup E] [inst_5 : SubtractionMonoid G] [AddMo
noidHomClass F E G] {f : F},   Measurable ⇑f →     ProbabilityTheory.HasIndepInc
rements X P → ProbabilityTheory.HasIndepIncrements (fun t ω => f (X t ω)) P
参数：fun t ω => f (X t ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.iIndepFun.comp`：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ :
 MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {γ : ι →
 Type u_11} {mβ : (i :…
-/
protected lemma HasIndepIncrements.map' {F G : Type*} [MeasurableSpace G] [FunLike F E G]
    [AddGroup E] [SubtractionMonoid G] [AddMonoidHomClass F E G] {f : F} (hf : Measurable f)
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω ↦ f (X t ω)) P := by
  intro n t ht
  simp_rw [← map_sub]
  exact (hX n t ht).comp (fun _ ↦ f) (fun _ ↦ hf)
/-
**ProbabilityTheory.HasIndepIncrements.map** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] {R : Type u_4} {F : Type u_5} [inst_2 : Semiring R]   [inst_3 : S
eminormedAddCommGroup E] [inst_4 : _root_.Module R E] [OpensMeasurableSpace E]  
 [inst_6 : SeminormedAddCommGroup F] [inst_7 : _root_.Module R F] [inst_8 : Meas
urableSpace F] [BorelSpace F]   (L : E →L[R] F),   ProbabilityTheory.HasIndepInc
rements X P → ProbabilityTheory.HasIndepIncrements (fun t ω => L (X t ω)) P
参数：L : E →L[R] F；fun t ω => L (X t ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasIndepIncrements.map'`：∀ {T : Type u_1} {Ω : Type u_
2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : T 
→ Ω → E}   [inst : Preorder T] …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
-/
protected lemma HasIndepIncrements.map {R F : Type*} [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [OpensMeasurableSpace E] [SeminormedAddCommGroup F] [Module R F]
    [MeasurableSpace F] [BorelSpace F] (L : E →L[R] F) (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω ↦ L (X t ω)) P :=
  hX.map' L.measurable
/-
**ProbabilityTheory.HasIndepIncrements.smul** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] {R : Type u_4} [inst_2 : AddGroup E] [inst_3 : DistribSMul R E]  
 [MeasurableConstSMul R E],   ProbabilityTheory.HasIndepIncrements X P → ∀ (c : 
R), ProbabilityTheory.HasIndepIncrements (fun t ω => c • X t ω) P
参数：c : R；fun t ω => c • X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasIndepIncrements.map'`：∀ {T : Type u_1} {Ω : Type u_
2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : T 
→ Ω → E}   [inst : Preorder T] …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
protected lemma HasIndepIncrements.smul {R : Type*} [AddGroup E] [DistribSMul R E]
    [MeasurableConstSMul R E] (hX : HasIndepIncrements X P) (c : R) :
    HasIndepIncrements (fun t ω ↦ c • (X t ω)) P :=
  hX.map' (f := DistribSMul.toAddMonoidHom E c) (MeasurableConstSMul.measurable_const_smul c)
/-
**ProbabilityTheory.HasIndepIncrements.neg** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.HasIndepIncrements`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst : Preorder T] [inst_1 : Meas
urableSpace E] [inst_2 : AddCommGroup E] [MeasurableNeg E],   ProbabilityTheory.
HasIndepIncrements X P → ProbabilityTheory.HasIndepIncrements (-X) P
参数：-X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasIndepIncrements.map'`：∀ {T : Type u_1} {Ω : Type u_
2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : T 
→ Ω → E}   [inst : Preorder T] …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
-/
protected lemma HasIndepIncrements.neg [AddCommGroup E] [MeasurableNeg E]
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (-X) P :=
  hX.map' (f := negAddMonoidHom) measurable_neg

end ProbabilityTheory

