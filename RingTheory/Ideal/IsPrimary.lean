/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
module

public import Mathlib.RingTheory.IsPrimary
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary ideals

A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`.

## Main definitions

- `Ideal.IsPrimary`

## Implementation details

Uses a specialized phrasing of `Submodule.IsPrimary` to have better API-piercing usage.

-/

public section

namespace Ideal

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A proper ideal `I` is primary as a submodule. -/
/-
**Ideal.IsPrimary** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal`。
形式化陈述：IsPrimary (I : Ideal R) : Prop
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper ideal `I` is primary as a submodule.
-/
abbrev IsPrimary (I : Ideal R) : Prop :=
  Submodule.IsPrimary I

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
/-
**Ideal.isPrimary_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isPrimary_iff {I : Ideal R} : I.IsPrimary ↔ I != ⊤ ∧ forall {x y : R}, x *
 y in I -> x in I ∨ y in radical I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrimary.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (I : Idea
l R), I.IsPrimary = Submodule.IsPrimary I
· 使用定理 `Submodule.IsPrimary.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (S : Submodu
le R M), S.IsP…
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`.
-/
lemma isPrimary_iff {I : Ideal R} :
    I.IsPrimary ↔ I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I := by
  rw [IsPrimary, Submodule.IsPrimary, forall_comm]
  simp only [mul_comm, mem_radical_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]
/-
**Ideal.IsPrime.isPrimary** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {I : Ideal R}, I.IsPrime → I.IsPr
imary
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ideal.isPrimary_iff`：isPrimary_iff {I : Ideal R} : I.IsPrimary ↔ I != ⊤ 
∧ forall {x y : R}, x * y in I -> x in I ∨ y in radical I
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem IsPrime.isPrimary {I : Ideal R} (hi : IsPrime I) : I.IsPrimary :=
  isPrimary_iff.mpr
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩
/-
**Ideal.isPrime_radical** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_radical {I : Ideal R} (hi : I.IsPrimary) : IsPrime (radical I)
参数：hi : I.IsPrimary。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsPrimary.isPrime_radical_colon`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   {S : Submodule R M}, S.IsP…
· 使用定理 `Submodule.colon_univ`：colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon 
Set.univ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
-/
theorem isPrime_radical {I : Ideal R} (hi : I.IsPrimary) : IsPrime (radical I) :=
  I.colon_univ ▸ hi.isPrime_radical_colon
/-
**Ideal.isPrimary_of_isMaximal_radical** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrimary_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) 
: I.IsPrimary
参数：hi : IsMaximal (radical I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.isPrimary_iff`：isPrimary_iff {I : Ideal R} : I.IsPrimary ↔ I != ⊤ 
∧ forall {x y : R}, x * y in I -> x in I ∨ y in radical I
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.radical_top`：radical_top : (radical ⊤ : Ideal R) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `add_le_iff`：add_le_iff : a + b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isPrimary_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) :
    I.IsPrimary := by
  rw [isPrimary_iff]
  constructor
  · rintro rfl
    exact (radical_top R ▸ hi).ne_top rfl
  · intro x y hxy
    by_cases h : I + span {y} = ⊤
    · rw [← span_singleton_le_iff_mem, ← mul_top (span {x}), ← h, mul_add,
        span_singleton_mul_span_singleton, add_le_iff, span_singleton_le_iff_mem]
      exact Or.inl ⟨mul_le_right, hxy⟩
    · obtain ⟨m, hm, hy⟩ := exists_le_maximal (I + span {y}) h
      rw [add_le_iff, span_singleton_le_iff_mem, ← hm.isPrime.radical_le_iff] at hy
      exact Or.inr (hi.eq_of_le hm.ne_top hy.1 ▸ hy.2)
/-
**Ideal.IsPrimary.inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrimary`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {I J : Ideal R},   I.IsPrimary → 
J.IsPrimary → I.radical = J.radical → (I ⊓ J).IsPrimary
参数：I ⊓ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsPrimary.inf`：∀ {R : Type u_1} {M : Type u_2} [inst : CommSem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S T : Submod
ule R M},   S…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.colon_univ`：colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon 
Set.univ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
-/
theorem IsPrimary.inf {I J : Ideal R} (hi : I.IsPrimary) (hj : J.IsPrimary)
    (hij : radical I = radical J) : (I ⊓ J).IsPrimary :=
  Submodule.IsPrimary.inf hi hj (by simpa)
/-
**Ideal.isPrimary_finsetInf** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isPrimary_finsetInf {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i 
in s) (hs : forall ⦃y⦄, y in s -> (f y).IsPrimary) (hs' : forall ⦃y⦄, y in s -> 
(f y).radical = (f i).radical) : IsPrimary (s.inf f)
参数：hi : i in s；hs : forall ⦃y⦄, y in s -> (f y).IsPrimary；hs' : forall ⦃y⦄, y in
 s -> (f y).radical = (f i).radical。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.isPrimary_finsetInf`：isPrimary_finsetInf {ι : Type*} {s : Fins
et ι} {f : ι -> Submodule R M} {i : ι} (hi : i in s) (hs : forall ⦃y⦄, y in s ->
 (f y).IsPrimary) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.colon_univ`：colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon 
Set.univ = I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
-/
lemma isPrimary_finsetInf {ι} {s : Finset ι} {f : ι → Ideal R} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).IsPrimary)
    (hs' : ∀ ⦃y⦄, y ∈ s → (f y).radical = (f i).radical) :
    IsPrimary (s.inf f) :=
  Submodule.isPrimary_finsetInf hi hs (by simpa)

@[deprecated (since := "2026-01-19")]
alias isPrimary_finset_inf := isPrimary_finsetInf
/-
**Ideal.IsPrimary.comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrimary`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] {I : Ideal S},   I.IsPrimary → ∀ (φ : R →+* S), (Ideal.comap φ I).IsPrim
ary
参数：φ : R →+* S；Ideal.comap φ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.isPrimary_iff`：isPrimary_iff {I : Ideal R} : I.IsPrimary ↔ I != ⊤ 
∧ forall {x y : R}, x * y in I -> x in I ∨ y in radical I
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma IsPrimary.comap {I : Ideal S} (hI : I.IsPrimary) (φ : R →+* S) : (I.comap φ).IsPrimary := by
  rw [isPrimary_iff] at hI ⊢
  refine hI.imp (comap_ne_top φ) fun h ↦ ?_
  simp only [mem_comap, map_mul, ← comap_radical]
  exact h

end Ideal

