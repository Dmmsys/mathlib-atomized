/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Metrizable.Real

/-!
# Limsup and liminf of reals

This file compiles filter-related results about `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

public section


open Filter ENNReal
open scoped NNReal

namespace Real
variable {ι : Type*} {f : Filter ι} {u : ι → ℝ}

@[simp]
/-
**Real.limsSup_of_not_isCobounded** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsSup_of_not_isCobounded {f : Filter Real} (hf : ¬ f.IsCobounded (· <= ·
)) : limsSup f = 0
参数：hf : ¬ f.IsCobounded (· <= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsSup.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsSup = sInf {a | ∀ᶠ (n : α) in f, n ≤ a}
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0
-/
lemma limsSup_of_not_isCobounded {f : Filter ℝ} (hf : ¬ f.IsCobounded (· ≤ ·)) :
    limsSup f = 0 := by rwa [limsSup, sInf_of_not_bddBelow]

@[simp]
/-
**Real.limsSup_of_not_isBounded** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsSup_of_not_isBounded {f : Filter Real} (hf : ¬ f.IsBounded (· <= ·)) :
 limsSup f = 0
参数：hf : ¬ f.IsBounded (· <= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsSup.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsSup = sInf {a | ∀ᶠ (n : α) in f, n ≤ a}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
-/
lemma limsSup_of_not_isBounded {f : Filter ℝ} (hf : ¬ f.IsBounded (· ≤ ·)) : limsSup f = 0 := by
  rw [limsSup]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/-
**Real.limsInf_of_not_isCobounded** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsInf_of_not_isCobounded {f : Filter Real} (hf : ¬ f.IsCobounded (· >= ·
)) : limsInf f = 0
参数：hf : ¬ f.IsCobounded (· >= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsInf.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsInf = sSup {a | ∀ᶠ (n : α) in f, a ≤ n}
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
-/
lemma limsInf_of_not_isCobounded {f : Filter ℝ} (hf : ¬ f.IsCobounded (· ≥ ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
/-
**Real.limsInf_of_not_isBounded** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsInf_of_not_isBounded {f : Filter Real} (hf : ¬ f.IsBounded (· >= ·)) :
 limsInf f = 0
参数：hf : ¬ f.IsBounded (· >= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsInf.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsInf = sSup {a | ∀ᶠ (n : α) in f, a ≤ n}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
-/
lemma limsInf_of_not_isBounded {f : Filter ℝ} (hf : ¬ f.IsBounded (· ≥ ·)) : limsInf f = 0 := by
  rw [limsInf]
  convert! sSup_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/-
**Real.limsup_of_not_isCoboundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsup_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· <= ·) u) : li
msup u f = 0
参数：hf : ¬ f.IsCoboundedUnder (· <= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.limsSup_of_not_isCobounded`：limsSup_of_not_isCobounded {f : Filter 
Real} (hf : ¬ f.IsCobounded (· <= ·)) : limsSup f = 0
-/
lemma limsup_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isCobounded hf

@[simp]
/-
**Real.limsup_of_not_isBoundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· <= ·) u) : limsup
 u f = 0
参数：hf : ¬ f.IsBoundedUnder (· <= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.limsSup_of_not_isBounded`：limsSup_of_not_isBounded {f : Filter Real
} (hf : ¬ f.IsBounded (· <= ·)) : limsSup f = 0
-/
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
/-
**Real.liminf_of_not_isCoboundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· >= ·) u) : li
minf u f = 0
参数：hf : ¬ f.IsCoboundedUnder (· >= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.limsInf_of_not_isCobounded`：limsInf_of_not_isCobounded {f : Filter 
Real} (hf : ¬ f.IsCobounded (· >= ·)) : limsInf f = 0
-/
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp]
/-
**Real.liminf_of_not_isBoundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：liminf_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· >= ·) u) : liminf
 u f = 0
参数：hf : ¬ f.IsBoundedUnder (· >= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.limsInf_of_not_isBounded`：limsInf_of_not_isBounded {f : Filter Real
} (hf : ¬ f.IsBounded (· >= ·)) : limsInf f = 0
-/
lemma liminf_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isBounded hf

end Real

namespace NNReal
variable {ι : Type*} {f : Filter ι} {u : ι → ℝ≥0}

/-
**NNReal.isBoundedUnder_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Type u_1} {f : Filter ι} {u : ι → NNReal},   (Filter.IsBoundedUnder
 (fun x1 x2 => x1 ≤ x2) f fun i => ↑(u i)) ↔ Filter.IsBoundedUnder (fun x1 x2 =>
 x1 ≤ x2) f u
参数：Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) f fun i => ↑(u i)；fun x1 x2 => x
1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp, norm_cast] lemma isBoundedUnder_le_toReal :
    IsBoundedUnder (· ≤ ·) f (fun i ↦ (u i : ℝ)) ↔ IsBoundedUnder (· ≤ ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by filter_upwards [hb]; simp +contextual⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩
/-
**NNReal.isBoundedUnder_ge_toReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Type u_1} {f : Filter ι} {u : ι → NNReal},   (Filter.IsBoundedUnder
 (fun x1 x2 => x1 ≥ x2) f fun i => ↑(u i)) ↔ Filter.IsBoundedUnder (fun x1 x2 =>
 x1 ≥ x2) f u
参数：Filter.IsBoundedUnder (fun x1 x2 => x1 ≥ x2) f fun i => ↑(u i)；fun x1 x2 => x
1 ≥ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp, norm_cast] lemma isBoundedUnder_ge_toReal :
    IsBoundedUnder (· ≥ ·) f (fun i ↦ (u i : ℝ)) ↔ IsBoundedUnder (· ≥ ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by simpa⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩
/-
**NNReal.isCoboundedUnder_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Type u_1} {f : Filter ι} {u : ι → NNReal} [f.NeBot],   (Filter.IsCo
boundedUnder (fun x1 x2 => x1 ≤ x2) f fun i => ↑(u i)) ↔     Filter.IsCoboundedU
nder (fun x1 x2 => x1 ≤ x2) f u
参数：Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) f fun i => ↑(u i)；fun x1 x2 =>
 x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
@[simp, norm_cast] lemma isCoboundedUnder_le_toReal [f.NeBot] :
    IsCoboundedUnder (· ≤ ·) f (fun i ↦ (u i : ℝ)) ↔ IsCoboundedUnder (· ≤ ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, fun x _ ↦ by simpa [*] using hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    exact ⟨b, fun x hx ↦ hb _ (hx.exists.choose_spec.trans' (by simp)) hx⟩
/-
**NNReal.isCoboundedUnder_ge_toReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Type u_1} {f : Filter ι} {u : ι → NNReal},   (Filter.IsCoboundedUnd
er (fun x1 x2 => x1 ≥ x2) f fun i => ↑(u i)) ↔     Filter.IsCoboundedUnder (fun 
x1 x2 => x1 ≥ x2) f u
参数：Filter.IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) f fun i => ↑(u i)；fun x1 x2 =>
 x1 ≥ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
@[simp, norm_cast] lemma isCoboundedUnder_ge_toReal :
    IsCoboundedUnder (· ≥ ·) f (fun i ↦ (u i : ℝ)) ↔ IsCoboundedUnder (· ≥ ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ (by simp), fun x _ ↦ hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    refine ⟨b, fun x hx ↦ ?_⟩
    obtain hx₀ | hx₀ := le_total x 0
    · exact hx₀.trans hb₀
    · exact hb _ hx₀ hx

@[simp]
/-
**NNReal.limsSup_of_not_isBounded** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：limsSup_of_not_isBounded {f : Filter Real>=0} (hf : ¬ f.IsBounded (· <= ·)
) : limsSup f = 0
参数：hf : ¬ f.IsBounded (· <= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsSup.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsSup = sInf {a | ∀ᶠ (n : α) in f, n ≤ a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0) = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.sInf_empty`：sInf_empty : sInf (∅ : Set Real>=0) = 0
-/
lemma limsSup_of_not_isBounded {f : Filter ℝ≥0} (hf : ¬ f.IsBounded (· ≤ ·)) : limsSup f = 0 := by
  rw [limsSup, ← bot_eq_zero]
  convert! sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
/-
**NNReal.limsInf_of_not_isCobounded** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：limsInf_of_not_isCobounded {f : Filter Real>=0} (hf : ¬ f.IsCobounded (· >
= ·)) : limsInf f = 0
参数：hf : ¬ f.IsCobounded (· >= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsInf.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsInf = sSup {a | ∀ᶠ (n : α) in f, a ≤ n}
· 使用定理 `NNReal.sSup_of_not_bddAbove`：∀ {s : Set NNReal}, ¬BddAbove s → sSup s = 
0
-/
lemma limsInf_of_not_isCobounded {f : Filter ℝ≥0} (hf : ¬ f.IsCobounded (· ≥ ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
/-
**NNReal.limsup_of_not_isBoundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· <= ·) u) : limsup
 u f = 0
参数：hf : ¬ f.IsBoundedUnder (· <= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.limsSup_of_not_isBounded`：limsSup_of_not_isBounded {f : Filter Re
al>=0} (hf : ¬ f.IsBounded (· <= ·)) : limsSup f = 0
-/
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
/-
**NNReal.liminf_of_not_isCoboundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· >= ·) u) : li
minf u f = 0
参数：hf : ¬ f.IsCoboundedUnder (· >= ·) u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.limsInf_of_not_isCobounded`：limsInf_of_not_isCobounded {f : Filte
r Real>=0} (hf : ¬ f.IsCobounded (· >= ·)) : limsInf f = 0
-/
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp, norm_cast]
/-
**NNReal.toReal_liminf** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：toReal_liminf : liminf (fun i => (u i : Real)) f = liminf u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Real.liminf_of_not_isCoboundedUnder`：liminf_of_not_isCoboundedUnder (hf 
: ¬ f.IsCoboundedUnder (· >= ·) u) : liminf u f = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `NNReal.liminf_of_not_isCoboundedUnder`：liminf_of_not_isCoboundedUnder (h
f : ¬ f.IsCoboundedUnder (· >= ·) u) : liminf u f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toReal_liminf : liminf (fun i ↦ (u i : ℝ)) f = liminf u f := by
  by_cases hf : f.IsCoboundedUnder (· ≥ ·) u; swap
  · simp [*]
  refine eq_of_forall_le_iff fun c ↦ ?_
  rw [← Real.toNNReal_le_iff_le_coe, le_liminf_iff (by simpa) ⟨0, by simp⟩, le_liminf_iff]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_comm (α := _ ≤ _)]
  refine forall₂_congr fun r hr ↦ ?_
  simpa using (le_or_gt 0 r).imp_right fun hr ↦ .of_forall fun i ↦ hr.trans_le (by simp)

@[simp, norm_cast]
/-
**NNReal.toReal_limsup** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：toReal_limsup : limsup (fun i => (u i : Real)) f = limsup u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `csInf_of_not_bddBelow`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α}, ¬BddBelow s → sInf s = sInf ∅
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `csInf_univ`：csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : s
Inf (univ : Set α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 34 条，此处仅展示前 30 条）
-/
lemma toReal_limsup : limsup (fun i ↦ (u i : ℝ)) f = limsup u f := by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  by_cases hf : f.IsBoundedUnder (· ≤ ·) u; swap
  · simp [*]
  have : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault
  refine eq_of_forall_le_iff fun c ↦ ?_
  rw [← Real.toNNReal_le_iff_le_coe, le_limsup_iff (by simpa) (by simpa), le_limsup_iff ‹_›]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_comm (α := _ ≤ _)]
  refine forall₂_congr fun r hr ↦ ?_
  simpa using (le_or_gt 0 r).imp_right fun hr ↦ .of_forall fun i ↦ hr.trans_le (by simp)

end NNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

/-
**ENNReal.eventually_le_limsup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：eventually_le_limsup [CountableInterFilter f] (u : α -> Real>=0∞) : forall
ᶠ y in f, u y <= f.limsup u
参数：u : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_le_limsup`：eventually_le_limsup (hf : IsBoundedUnder (· <= ·)
 f u
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
theorem eventually_le_limsup [CountableInterFilter f] (u : α → ℝ≥0∞) :
    ∀ᶠ y in f, u y ≤ f.limsup u :=
  _root_.eventually_le_limsup
/-
**ENNReal.limsup_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_eq_zero_iff [CountableInterFilter f] {u : α -> Real>=0∞} : f.limsup
 u = 0 ↔ u =ᶠ[f] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsup_eq_bot`：limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α → ℝ≥0∞} :
    f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  limsup_eq_bot
/-
**ENNReal.limsup_const_mul_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_const_mul_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a 
!= ⊤) : (f.limsup fun x : α => a * u x) = a * f.limsup u
参数：ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
· 使用定理 `ENNReal.mul_inv_cancel_left`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (a⁻¹
 * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.limsup_apply`：OrderIso.limsup_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
theorem limsup_const_mul_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    (f.limsup fun x : α => a * u x) = a * f.limsup u := by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x ↦
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.limsup_apply.symm
/-
**ENNReal.limsup_mul_const_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_mul_const_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a 
!= ⊤) : f.limsup (fun x : α => u x * a) = a * f.limsup u
参数：ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.limsup_const_mul_of_ne_top`：limsup_const_mul_of_ne_top {u : α ->
 Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) : (f.limsup fun x : α => a * u x) = 
a * f.limsup u
-/
theorem limsup_mul_const_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    f.limsup (fun x : α => u x * a) = a * f.limsup u := by
  simpa [mul_comm] using limsup_const_mul_of_ne_top ha_top
/-
**ENNReal.liminf_const_mul_of_ne_zero_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
形式化陈述：liminf_const_mul_of_ne_zero_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (
ha₀ : a != 0) (ha_top : a != ⊤) : f.liminf (fun x : α => a * u x) = a * f.liminf
 u
参数：ha₀ : a != 0；ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
· 使用定理 `ENNReal.mul_inv_cancel_left`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (a⁻¹
 * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.liminf_apply`：OrderIso.liminf_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem liminf_const_mul_of_ne_zero_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞}
    (ha₀ : a ≠ 0) (ha_top : a ≠ ⊤) :
    f.liminf (fun x : α => a * u x) = a * f.liminf u := by
  let g_iso := (ENNReal.mul_right_strictMono ha₀ ha_top).orderIsoOfSurjective _ fun x ↦
    ⟨a⁻¹ * x, ENNReal.mul_inv_cancel_left ha₀ ha_top⟩
  exact g_iso.liminf_apply.symm
/-
**ENNReal.liminf_mul_const_of_ne_zero_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
形式化陈述：liminf_mul_const_of_ne_zero_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (
ha₀ : a != 0) (ha_top : a != ⊤) : f.liminf (fun x : α => u x * a) = a * f.liminf
 u
参数：ha₀ : a != 0；ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.liminf_const_mul_of_ne_zero_of_ne_top`：liminf_const_mul_of_ne_ze
ro_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ⊤)
 : f.liminf (fun x : α => a * u x) …
-/
theorem liminf_mul_const_of_ne_zero_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞}
    (ha₀ : a ≠ 0) (ha_top : a ≠ ⊤) :
    f.liminf (fun x : α => u x * a) = a * f.liminf u := by
  simpa [mul_comm] using liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top
/-
**ENNReal.liminf_const_mul_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：liminf_const_mul_of_ne_top [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (h
a_top : a != ⊤) : f.liminf (fun x : α => a * u x) = a * f.liminf u
参数：ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `ENNReal.liminf_const_mul_of_ne_zero_of_ne_top`：liminf_const_mul_of_ne_ze
ro_of_ne_top {u : α -> Real>=0∞} {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ⊤)
 : f.liminf (fun x : α => a * u x) …
-/
theorem liminf_const_mul_of_ne_top [f.NeBot] {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    f.liminf (fun x : α => a * u x) = a * f.liminf u := by
  by_cases ha₀ : a = 0
  · simp_rw [ha₀, zero_mul, ← ENNReal.bot_eq_zero]
    apply liminf_const
  exact liminf_const_mul_of_ne_zero_of_ne_top ha₀ ha_top
/-
**ENNReal.liminf_mul_const_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：liminf_mul_const_of_ne_top [f.NeBot] {u : α -> Real>=0∞} {a : Real>=0∞} (h
a_top : a != ⊤) : f.liminf (fun x : α => u x * a) = a * f.liminf u
参数：ha_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.liminf_const_mul_of_ne_top`：liminf_const_mul_of_ne_top [f.NeBot]
 {u : α -> Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) : f.liminf (fun x : α => a
 * u x) = a * f.liminf u
-/
theorem liminf_mul_const_of_ne_top [f.NeBot] {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    f.liminf (fun x : α => u x * a) = a * f.liminf u := by
  simpa [mul_comm] using liminf_const_mul_of_ne_top ha_top
/-
**ENNReal.limsup_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_const_mul [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0
∞} : f.limsup (a * u ·) = a * f.limsup u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.limsup_const_mul_of_ne_top`：limsup_const_mul_of_ne_top {u : α ->
 Real>=0∞} {a : Real>=0∞} (ha_top : a != ⊤) : (f.limsup fun x : α => a * u x) = 
a * f.limsup u
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.not_eventually`：not_eventually {p : α -> Prop} {f : Filter α} : (
¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `limsup_eq_bot`：limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.top_mul'`：top_mul' : ∞ * a = if a = 0 then 0 else ∞
（共 33 条，此处仅展示前 30 条）
-/
theorem limsup_const_mul [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    f.limsup (a * u ·) = a * f.limsup u := by
  by_cases! ha_top : a ≠ ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_def, ← ENNReal.bot_eq_zero,
      limsup_const_bot]
    simp
  · have hu_mul : ∃ᶠ x : α in f, ⊤ ≤ ite (u x = 0) (0 : ℝ≥0∞) ⊤ := by
      rw [EventuallyEq, not_eventually] at hu
      exact hu.mono fun x hx => by simpa
    have h_top_le : (f.limsup fun x : α => ite (u x = 0) (0 : ℝ≥0∞) ⊤) = ⊤ :=
      eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)
    have hfu : f.limsup u ≠ 0 := mt limsup_eq_bot.1 hu
    simp [ha_top, top_mul', h_top_le, hfu]
/-
**ENNReal.limsup_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_mul_const [CountableInterFilter f] {u : α -> Real>=0∞} {a : Real>=0
∞} : f.limsup (u · * a) = a * f.limsup u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.limsup_const_mul`：limsup_const_mul [CountableInterFilter f] {u :
 α -> Real>=0∞} {a : Real>=0∞} : f.limsup (a * u ·) = a * f.limsup u
-/
theorem limsup_mul_const [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    f.limsup (u · * a) = a * f.limsup u := by
  simpa [mul_comm] using limsup_const_mul

/-- See also `limsup_mul_le'` -/
/-
**ENNReal.limsup_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_mul_le [CountableInterFilter f] (u v : α -> Real>=0∞) : f.limsup (u
 * v) <= f.limsup u * f.limsup v
参数：u v : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ENNReal.eventually_le_limsup`：eventually_le_limsup [CountableInterFilter
 f] (u : α -> Real>=0∞) : forallᶠ y in f, u y <= f.limsup u
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `ENNReal.limsup_const_mul`：limsup_const_mul [CountableInterFilter f] {u :
 α -> Real>=0∞} {a : Real>=0∞} : f.limsup (a * u ·) = a * f.limsup u

--- 原说明 ---
See also `limsup_mul_le'`
-/
theorem limsup_mul_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u * v) ≤ f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) ≤ f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul
/-
**ENNReal.limsup_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_add_le [CountableInterFilter f] (u v : α -> Real>=0∞) : f.limsup (u
 + v) <= f.limsup u + f.limsup v
参数：u v : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.eventually_le_limsup`：eventually_le_limsup [CountableInterFilter
 f] (u : α -> Real>=0∞) : forallᶠ y in f, u y <= f.limsup u
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
  sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))
/-
**ENNReal.limsup_liminf_le_liminf_limsup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [Countable
InterFilter f] {g : Filter β} (u : α -> β -> Real>=0∞) : (f.limsup fun a : α => 
g.liminf fun b : β => u a b) <= g.liminf fun b => f.limsup fun a => u a b
参数：u : α -> β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `ENNReal.eventually_le_limsup`：eventually_le_limsup [CountableInterFilter
 f] (u : α -> Real>=0∞) : forallᶠ y in f, u y <= f.limsup u
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α → β → ℝ≥0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) ≤
      g.liminf fun b => f.limsup fun a => u a b :=
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
  sInf_le <| h1.mono fun x hx => Filter.liminf_le_liminf (Filter.Eventually.of_forall hx)
/-
**ENNReal.ofReal_limsup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_limsup {u : α -> Real} (h₁ : IsCoboundedUnder (· <= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.eq_of_forall_le_nnreal_iff`：eq_of_forall_le_nnreal_iff {x y : Re
al>=0∞} : (forall r : Real>=0, x <= r ↔ y <= r) -> x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `ENNReal.toReal_lt_of_lt_ofReal`：toReal_lt_of_lt_ofReal {b : Real} (h : a
 < ENNReal.ofReal b) : ENNReal.toReal a < b
-/
lemma ofReal_limsup {u : α → ℝ}
    (h₁ : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ENNReal.ofReal (limsup u f) = limsup (fun a ↦ .ofReal (u a)) f := by
  refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
  simp only [ofReal_le_coe]
  rw [limsup_le_iff, limsup_le_iff]
  constructor
  · rintro h (_ | x) hx
    · simp
    filter_upwards [h x (by simpa using hx)] with a ha
    obtain ha₀ | ha₀ := le_total (u a) 0
    · simpa [ofReal_of_nonpos, *] using hx.bot_lt
    · simp [ofReal_lt_coe_iff, *]
  · rintro h x hx
    have : 0 < x := hx.trans_le' (by simp)
    filter_upwards [h (.ofReal x) (by simpa [this] using hx)] with a ha
    exact (toReal_lt_of_lt_ofReal ha).trans_le' (by simp [toReal_ofReal'])
/-
**ENNReal.ofReal_limsup_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_limsup_toReal [f.NeBot] {u : α -> Real>=0∞} {C : Real>=0} (hf : for
allᶠ a in f, u a <= C) : ENNReal.ofReal (limsup (fun a => (u a).toReal) f) = lim
sup u f
参数：hf : forallᶠ a in f, u a <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用引理 `Filter.isBoundedUnder_of_eventually_le`：isBoundedUnder_of_eventually_le 
{a : α} (h : forallᶠ x in f, u x <= a) : IsBoundedUnder (· <= ·) f u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_le_coe_of_le_coe`：toReal_le_coe_of_le_coe {a : Real>=0∞} 
{b : Real>=0} (h : a <= b) : a.toReal <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENNReal.ofReal_limsup`：ofReal_limsup {u : α -> Real} (h₁ : IsCoboundedUn
der (· <= ·) f u
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma ofReal_limsup_toReal [f.NeBot] {u : α → ℝ≥0∞} {C : ℝ≥0} (hf : ∀ᶠ a in f, u a ≤ C) :
    ENNReal.ofReal (limsup (fun a ↦ (u a).toReal) f) = limsup u f := by
  have h₁ : IsCoboundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) :=
    IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ by positivity
  have h₂ : IsBoundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    exact ENNReal.toReal_le_coe_of_le_coe ha
  refine (ENNReal.ofReal_limsup h₁ h₂).trans (limsup_congr ?_)
  filter_upwards [hf] with x hx
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp : C ≠ ∞) hx)
/-
**ENNReal.toReal_limsup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：toReal_limsup {u : α -> Real>=0∞} (h₁ : forallᶠ a in f, u a != ∞) (h₂ : Is
BoundedUnder (· <= ·) f fun a => (u a).toReal
参数：h₁ : forallᶠ a in f, u a != ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `sInf_univ`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf Set.univ = 
⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `csInf_of_not_bddBelow`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α}, ¬BddBelow s → sInf s = sInf ∅
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
（共 42 条，此处仅展示前 30 条）
-/
lemma toReal_limsup {u : α → ℝ≥0∞} (h₁ : ∀ᶠ a in f, u a ≠ ∞)
    (h₂ : IsBoundedUnder (· ≤ ·) f fun a ↦ (u a).toReal := by isBoundedDefault) :
    (limsup u f).toReal = limsup (fun a ↦ (u a).toReal) f := by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  have : IsCoboundedUnder (· ≤ ·) f fun a ↦ (u a).toReal := .of_frequently_ge (a := 0) (by simpa)
  refine eq_of_forall_ge_iff fun r ↦ ?_
  obtain hr | hr := lt_or_ge r 0
  · exact iff_of_false (hr.trans_le toReal_nonneg).not_ge
      (hr.trans_le <| le_limsup_of_frequently_le (by simpa)).not_ge
  rw [← le_ofReal_iff_toReal_le _ hr, limsup_le_iff, limsup_le_iff]
  constructor
  · rintro h x hx
    have : 0 < x := hx.trans_le' hr
    filter_upwards [h (.ofReal x) (by simpa [this] using hx)] with i hi
    exact toReal_lt_of_lt_ofReal hi
  · rintro h (_ | x) hx
    · simpa [lt_top_iff_ne_top]
    filter_upwards [h₁, h x (by simpa [ofReal_lt_coe_iff hr] using hx)] with i hi
    simp [← lt_ofReal_iff_toReal_lt hi]
  obtain ⟨x, hx⟩ := h₂
  rw [eventually_map] at hx
  have hx₀ : 0 ≤ x := by obtain ⟨i, hi⟩ := hx.exists; exact toReal_nonneg.trans hi
  simp only [limsup, limsSup, eventually_map, ne_eq, sInf_eq_top, Set.mem_ofPred_eq, not_forall]
  refine ⟨.ofReal x, ?_, by simp⟩
  filter_upwards [h₁, hx] with i hi
  simp [le_ofReal_iff_toReal_le, *]

end ENNReal

