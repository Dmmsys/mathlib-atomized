/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
## Gauss's Lemma for Dedekind Domains

This file contains Gauss's Lemma for Dedekind Domains, which states that the content ideal of a
polynomial is the whole ring if and only if the `v`-adic Gauss norms of the polynomial are equal to
1 for all `v`.
-/

public section
namespace Polynomial

open IsDedekindDomain HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {b : NNReal}
  (hb : 1 < b) (p : R[X])

/-
**Polynomial.gaussNorm_intAdicAbv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_intAdicAbv_le_one : p.gaussNorm (v.intAdicAbv hb) 1 <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem gaussNorm_intAdicAbv_le_one : p.gaussNorm (v.intAdicAbv hb) 1 ≤ 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  simp [gaussNorm, hp0, intAdicAbv_le_one]

/-- Given a polynomial `p` in `R[X]`, the `v`-adic Gauss norm of `p` is smaller than 1 if and only
if the content ideal of `p` is contained in the prime ideal corresponding to `v`. -/
/-
**Polynomial.gaussNorm_lt_one_iff_contentIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：gaussNorm_lt_one_iff_contentIdeal_le : p.gaussNorm (v.intAdicAbv hb) 1 < 1
 ↔ p.contentIdeal <= v.asIdeal
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
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Polynomial.contentIdeal_zero`：contentIdeal_zero : (0 : R[X]).contentIdea
l = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_lt_one_iff`：intAdicAbv_lt_
one_iff : v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.le_sup'_of_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eSup α] {s : Finset β} (f : β → α) {a : α} {b : β} (hb : b ∈ s),   a ≤ f b → a ≤
 s.sup' ⋯ …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Given a polynomial `p` in `R[X]`, the `v`-adic Gauss norm of `p` is smaller than
 1 if and only
if the content ideal of `p` is contained in the prime ideal corresponding to `v`
.
-/
theorem gaussNorm_lt_one_iff_contentIdeal_le :
    p.gaussNorm (v.intAdicAbv hb) 1 < 1 ↔ p.contentIdeal ≤ v.asIdeal := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsupp_nonempty : p.support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, one_pow, mul_one, contentIdeal, Ideal.span_le,
    Set.subset_def, SetLike.mem_coe, ← v.intAdicAbv_lt_one_iff hb]
  constructor
  · contrapose!
    simp only [mem_coeffs_iff, mem_support_iff, ↓existsAndEq, and_true, forall_exists_index,
      and_imp]
    intro _ h1 h2
    exact Finset.le_sup'_of_le (fun n ↦ (v.intAdicAbv hb) (p.coeff n)) (by simp [h1]) h2
  · intro h
    rw [Finset.sup'_lt_iff]
    intro n hn
    rw [mem_support_iff] at hn
    exact h _ <| p.coeff_mem_coeffs hn

/-- **Gauss's Lemma:** given a polynomial `p` in `R[X]`, the content ideal of `p` is the whole ring
if and only if the `v`-adic Gauss norms of `p` are equal to 1 for all `v`. -/
/-
**Polynomial.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：contentIdeal_eq_top_iff_forall_gaussNorm_eq_one (hR : ¬IsField R) : p.cont
entIdeal = ⊤ ↔ forall v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 =
 1
参数：hR : ¬IsField R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists`：ideal_ne_top
_iff_exists (hR : ¬IsField R) (I : Ideal R) : I != ⊤ ↔ exists P : HeightOneSpect
rum R, I <= P.asIdeal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Gauss's Lemma:** given a polynomial `p` in `R[X]`, the content ideal of `p` is
 the whole ring
if and only if the `v`-adic Gauss norms of `p` are equal to 1 for all `v`.
-/
theorem contentIdeal_eq_top_iff_forall_gaussNorm_eq_one (hR : ¬IsField R) :
    p.contentIdeal = ⊤ ↔ ∀ v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  convert_to _ ↔ ∀ (x : HeightOneSpectrum R), 1 ≤ gaussNorm (x.intAdicAbv hb) 1 p
  · grind [gaussNorm_intAdicAbv_le_one]
  simp [← not_iff_not, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (hR : ¬IsField R)
  {b : NNReal} (hb : 1 < b) (p : R[X])

include hR in
/-- In case `R` is PID, given a polynomial `p` in `R[X]`, `p` is primitive if and only if the
`v`-adic Gauss norms of `p` are equal to 1 for all `v`. -/
/-
**Polynomial.isPrimitive_iff_forall_gaussNorm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：isPrimitive_iff_forall_gaussNorm_eq_one : p.IsPrimitive ↔ forall v : Heigh
tOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isPrimitive_iff_contentIdeal_eq_top`：isPrimitive_iff_contentI
deal_eq_top : p.IsPrimitive ↔ p.contentIdeal = ⊤
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `Polynomial.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one`：contentIdeal
_eq_top_iff_forall_gaussNorm_eq_one (hR : ¬IsField R) : p.contentIdeal = ⊤ ↔ for
all v : HeightOneSpectrum R, p.gaussNorm (v.intA…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In case `R` is PID, given a polynomial `p` in `R[X]`, `p` is primitive if and on
ly if the
`v`-adic Gauss norms of `p` are equal to 1 for all `v`.
-/
theorem isPrimitive_iff_forall_gaussNorm_eq_one :
    p.IsPrimitive ↔ ∀ v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  rw [isPrimitive_iff_contentIdeal_eq_top, p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one hb hR]

end Polynomial

