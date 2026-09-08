/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
public import Mathlib.ModelTheory.Algebra.Field.Basic

/-!
# First-order theory of fields

This file defines the first-order theory of fields of characteristic `p` as a theory over the
language of rings

## Main definitions

- `FirstOrder.Language.Theory.fieldOfChar` : the first-order theory of fields of characteristic `p`
  as a theory over the language of rings
-/

@[expose] public section

variable {p : ℕ} {K : Type*}

namespace FirstOrder

namespace Field

open Language FirstOrder.Ring

/-- For a given natural number `n`, `eqZero n` is the sentence in the language of rings
saying that `n` is zero. -/
/-
**FirstOrder.Field.eqZero** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Field`。
形式化陈述：eqZero (n : Nat) : Language.ring.Sentence
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a given natural number `n`, `eqZero n` is the sentence in the language of ri
ngs
saying that `n` is zero.
-/
noncomputable def eqZero (n : ℕ) : Language.ring.Sentence :=
  Term.equal (termOfFreeCommRing n) 0
/-
**FirstOrder.Field.realize_eqZero** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : FirstOrder.Ring.CompatibleR
ing K] (n : ℕ) (v : Empty → K),   FirstOrder.Language.Formula.Realize (FirstOrde
r.Field.eqZero n) v ↔ ↑n = 0
参数：n : ℕ；v : Empty → K；FirstOrder.Field.eqZero n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Ring.realize_termOfFreeCommRing`：realize_termOfFreeCommRing (
p : FreeCommRing α) (v : α -> R) : (termOfFreeCommRing p).realize v = FreeCommRi
ng.lift v p
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `FirstOrder.Ring.realize_zero`：realize_zero (v : α -> R) : Term.realize v
 (0 : ring.Term α) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem realize_eqZero [CommRing K] [CompatibleRing K] (n : ℕ)
    (v : Empty → K) : (Formula.Realize (eqZero n) v) ↔ ((n : K) = 0) := by
  simp [eqZero]

/-- The first-order theory of fields of characteristic `p` as a theory over the language of rings -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**FirstOrder.Field._root_.FirstOrder.Language.Theory.fieldOfChar** 是 Mathlib 中的一
个定义，位于命名空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def _root_.FirstOrder.Language.Theory.fieldOfChar (p : ℕ) : Language.ring.Theory :=
  Theory.field ∪
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : ℕ | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}
/-
**FirstOrder.Field.model_hasChar_of_charP** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.
Field`。
形式化陈述：model_hasChar_of_charP [Field K] [CompatibleRing K] [CharP K p] : (Theory.
fieldOfChar p).Model K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.model_union_iff`：model_union_iff {T' : L.Theo
ry} : M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T'
· 使用定理 `FirstOrder.Field.instModelField`：∀ {K : Type u_1} [inst : Field K] [inst
_1 : FirstOrder.Ring.CompatibleRing K], K ⊨ FirstOrder.Language.Theory.field
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance model_hasChar_of_charP [Field K] [CompatibleRing K] [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  refine Language.Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_true, Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq,
      Sentence.Realize, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Formula.realize_not, realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact CharP.charP_to_charZero K
/-
**FirstOrder.Field.charP_iff_model_fieldOfChar** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Field`。
形式化陈述：charP_iff_model_fieldOfChar [Field K] [CompatibleRing K] : (Theory.fieldOf
Char p).Model K ↔ CharP K p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FirstOrder.Field.instModelField`：∀ {K : Type u_1} [inst : Field K] [inst
_1 : FirstOrder.Ring.CompatibleRing K], K ⊨ FirstOrder.Language.Theory.field
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CharP.charP_iff_prime_eq_zero`：charP_iff_prime_eq_zero [Nontrivial R] {p
 : Nat} (hp : p.Prime) : CharP R p ↔ (p : R) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charP_iff_model_fieldOfChar [Field K] [CompatibleRing K] :
    (Theory.fieldOfChar p).Model K ↔ CharP K p := by
  simp only [Theory.fieldOfChar, Theory.model_union_iff,
    (show (Theory.field.Model K) by infer_instance), true_and]
  split_ifs with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_ofPred_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Formula.realize_not,
      realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact ⟨fun _ => CharP.ofCharZero _, fun _ => CharP.charP_to_charZero K⟩
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize, forall_eq,
      realize_eqZero, ← CharP.charP_iff_prime_eq_zero hp]
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize,
      forall_eq, Formula.realize_bot, false_iff]
    intro H
    cases (CharP.char_is_prime_or_zero K p) <;> simp_all
/-
**FirstOrder.Field.model_fieldOfChar_of_charP** 是 Mathlib 中的一个实例，位于命名空间 `FirstOr
der.Field`。
形式化陈述：model_fieldOfChar_of_charP [Field K] [CompatibleRing K] [CharP K p] : (The
ory.fieldOfChar p).Model K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Field.charP_iff_model_fieldOfChar`：charP_iff_model_fieldOfCha
r [Field K] [CompatibleRing K] : (Theory.fieldOfChar p).Model K ↔ CharP K p
-/
instance model_fieldOfChar_of_charP [Field K] [CompatibleRing K]
    [CharP K p] : (Theory.fieldOfChar p).Model K :=
  charP_iff_model_fieldOfChar.2 inferInstance

variable (p) (K)
/- Not an instance because it caused performance problems in a different file. -/
/-
**FirstOrder.Field.charP_of_model_fieldOfChar** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Field`。
形式化陈述：charP_of_model_fieldOfChar [Field K] [CompatibleRing K] [h : (Theory.field
OfChar p).Model K] : CharP K p
参数：Theory.fieldOfChar p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Field.charP_iff_model_fieldOfChar`：charP_iff_model_fieldOfCha
r [Field K] [CompatibleRing K] : (Theory.fieldOfChar p).Model K ↔ CharP K p

--- 原说明 ---
Not an instance because it caused performance problems in a different file.
-/
theorem charP_of_model_fieldOfChar [Field K] [CompatibleRing K]
    [h : (Theory.fieldOfChar p).Model K] : CharP K p :=
  charP_iff_model_fieldOfChar.1 h

end Field

end FirstOrder

