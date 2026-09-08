/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# M-structure

A projection P on a normed space X is said to be an L-projection (`IsLprojection`) if, for all `x`
in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

A projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

The L-projections on `X` form a Boolean algebra (`IsLprojection.Subtype.BooleanAlgebra`).

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB\*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW\*-triple with predual `X`, the M-summands
of `A` are exactly the weak\*-closed ideals, and their pre-duals can be identified with the
L-summands of `X`. In the special case when `A` is a C\*-algebra, the M-ideals are exactly the
norm-closed two-sided ideals of `A`, when `A` is also a W\*-algebra the M-summands are exactly the
weak\*-closed two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`MeasureTheory.MeasurableSpace`.

Instead of using `P : X →L[𝕜] X` to represent projections, we use an arbitrary ring `M` with a
faithful action on `X`. `ContinuousLinearMap.apply_module` can be used to recover the `X →L[𝕜] X`
special case.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

@[expose] public section

variable (X : Type*) [NormedAddCommGroup X]
variable {M : Type*} [Ring M] [Module M X]


/-- A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
/-
**IsLprojection** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [inst : NormedAddCommGroup X] → {M : Type u_2} → [inst_1 
: Ring M] → [_root_.Module M X] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projection on a normed space `X` is said to be an L-projection if, for all `x`
 in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

Note that we write `P • x` instead of `P x` for reasons described in the module 
docstring.
-/
structure IsLprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Lnorm : ∀ x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖

/-- A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
/-
**IsMprojection** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [inst : NormedAddCommGroup X] → {M : Type u_2} → [inst_1 
: Ring M] → [_root_.Module M X] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projection on a normed space `X` is said to be an M-projection if, for all `x`
 in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

Note that we write `P • x` instead of `P x` for reasons described in the module 
docstring.
-/
structure IsMprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Mnorm : ∀ x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖

variable {X}

namespace IsLprojection

-- TODO: The literature always uses uppercase 'L' for L-projections
/-
**IsLprojection.Lcomplement** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P)
参数：h : IsLprojection X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `IsLprojection.proj`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : 
Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojectio
n X P → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `IsLprojection.Lnorm`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M :
 Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojecti
on X P → …
-/
theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm, sub_sub_cancel]
    exact h.Lnorm x⟩
/-
**IsLprojection.Lcomplement_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P)
参数：P : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLprojection.Lcomplement`：Lcomplement {P : M} (h : IsLprojection X P) :
 IsLprojection X (1 - P)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩
/-
**IsLprojection.commute** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLpro
jection X Q) : Commute P Q
参数：h₁ : IsLprojection X P；h₂ : IsLprojection X Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_sub_eq_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a b : 
E}, ‖a - b‖ = 0 ↔ a = b
· 使用定理 `IsLprojection.Lnorm`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M :
 Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojecti
on X P → …
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `IsLprojection.proj`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : 
Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojectio
n X P → …
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.MStructure.0.IsLprojection.commu
te._abel_1_1`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : Type u_2} [ins
t_1 : Ring M] [inst_2 : _root_.Module M X] {P : M}   (R : M) (x : X),   ‖R…
· 使用定理 `ge_iff_le`：∀ {α : Type u_1} [inst : LE α] {x y : α}, x ≥ y ↔ y ≤ x
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_le_insert'`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (u v : E
), ‖u‖ ≤ ‖v‖ + ‖u - v‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 90 条，此处仅展示前 30 条）
-/
theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    Commute P Q := by
  have PR_eq_RPR : ∀ R : M, IsLprojection X R → P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖(R * R) • x - R • P • R • x‖ + ‖(1 - R) • (1 - P) • R • x‖) := by
            rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) • R • x), sub_smul 1 P, one_smul, smul_sub,
              mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖((1 - R) * R) • x - (1 - R) • P • R • x‖) := by
            rw [h₃.proj.eq, sub_smul 1 P, one_smul, smul_sub, mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖(1 - R) • P • R • x‖) := by
            rw [sub_mul, h₃.proj.eq, one_mul, sub_self, zero_smul, zero_sub, norm_neg]
          _ = ‖R • P • R • x‖ + ‖R • x - R • P • R • x‖ + 2 • ‖(1 - R) • P • R • x‖ := by abel
          _ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ := by
            rw [ge_iff_le]
            have :=
              add_le_add_left (norm_le_insert' (R • x) (R • P • R • x)) (2 • ‖(1 - R) • P • R • x‖)
            simpa only [mul_smul, sub_smul, one_smul] using this
      rw [two_smul] at e1
      nlinarith [e1, norm_nonneg ((P * R) • x - (R * P * R) • x)]
  have QP_eq_QPQ : Q * P = Q * P * Q := by
    have e1 : Q * P - Q * P * Q = 0 := by
      calc
        Q * P - Q * P * Q = P * (1 - Q) - (1 - Q) * P * (1 - Q) := by noncomm_ring
        _ = 0 := sub_eq_zero.mpr (PR_eq_RPR (1 - Q) h₂.Lcomplement)
    simpa [sub_eq_zero] using e1
  change P * Q = Q * P
  rw [QP_eq_QPQ, PR_eq_RPR Q h₂]
/-
**IsLprojection.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLproject
ion X Q) : IsLprojection X (P * Q)
参数：h₁ : IsLprojection X P；h₂ : IsLprojection X Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.mul_of_commute`：mul_of_commute (hab : Commute a b) (ha 
: IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b)
· 使用定理 `IsLprojection.commute`：commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLpro
jection X P) (h₂ : IsLprojection X Q) : Commute P Q
· 使用定理 `IsLprojection.proj`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : 
Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojectio
n X P → …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsLprojection.Lnorm`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M :
 Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojecti
on X P → …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]
/-
**IsLprojection.join** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojec
tion X Q) : IsLprojection X (P + Q - P * Q)
参数：h₁ : IsLprojection X P；h₂ : IsLprojection X Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.MStructure.0.IsLprojection.join.
_abel_1_1`：∀ {M : Type u_1} [inst : Ring M] {P Q : M}, P + Q + -(P * Q) = 1 + -(
1 + -P + -(Q + -(P * Q)))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLprojection.Lcomplement_iff`：Lcomplement_iff (P : M) : IsLprojection X
 P ↔ IsLprojection X (1 - P)
· 使用定理 `IsLprojection.mul`：mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection 
X P) (h₂ : IsLprojection X Q) : IsLprojection X (P * Q)
· 使用定理 `IsLprojection.Lcomplement`：Lcomplement {P : M} (h : IsLprojection X P) :
 IsLprojection X (1 - P)
-/
theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert! (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring
/-
**IsLprojection.Subtype.instCompl** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subty
pe`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} → [i
nst_1 : Ring M] → [inst_2 : _root_.Module M X] → Compl { f // IsLprojection X f 
}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.instCompl : Compl { f : M // IsLprojection X f } :=
  ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]
/-
**IsLprojection.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_compl (P : { P : M // IsLprojection X P }) : ↑Pᶜ = (1 : M) - ↑P
参数：P : { P : M // IsLprojection X P }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compl (P : { P : M // IsLprojection X P }) : ↑Pᶜ = (1 : M) - ↑P :=
  rfl
/-
**IsLprojection.Subtype.inf** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → Min 
{ P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.inf [FaithfulSMul M X] : Min { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]
/-
**IsLprojection.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) : ↑(P ⊓ 
Q) = (↑P : M) * ↑Q
参数：P Q : { P : M // IsLprojection X P }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊓ Q) = (↑P : M) * ↑Q :=
  rfl
/-
**IsLprojection.Subtype.sup** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → Max 
{ P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.sup [FaithfulSMul M X] : Max { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]
/-
**IsLprojection.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) : ↑(P ⊔ 
Q) = (↑P : M) + ↑Q - ↑P * ↑Q
参数：P Q : { P : M // IsLprojection X P }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊔ Q) = (↑P : M) + ↑Q - ↑P * ↑Q :=
  rfl
/-
**IsLprojection.Subtype.sdiff** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → SDif
f { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.sdiff [FaithfulSMul M X] : SDiff { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]
/-
**IsLprojection.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) : ↑(P 
\ Q) = (↑P : M) * (1 - ↑Q)
参数：P Q : { P : M // IsLprojection X P }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P \ Q) = (↑P : M) * (1 - ↑Q) :=
  rfl
/-
**IsLprojection.Subtype.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Su
btype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → Part
ialOrder { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.partialOrder [FaithfulSMul M X] :
    PartialOrder { P : M // IsLprojection X P } where
  le P Q := (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁, mul_assoc, ← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.ext (by convert! (P.prop.commute Q.prop).eq)
/-
**IsLprojection.le_def** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) : P <= Q 
↔ (P : M) = ↑(P ⊓ Q)
参数：P Q : { P : M // IsLprojection X P }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    P ≤ Q ↔ (P : M) = ↑(P ⊓ Q) :=
  Iff.rfl
/-
**IsLprojection.Subtype.zero** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} → [i
nst_1 : Ring M] → [inst_2 : _root_.Module M X] → Zero { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.zero : Zero { P : M // IsLprojection X P } :=
  ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]
/-
**IsLprojection.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl
/-
**IsLprojection.Subtype.one** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} → [i
nst_1 : Ring M] → [inst_2 : _root_.Module M X] → One { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.one : One { P : M // IsLprojection X P } :=
  ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.Lcomplement⟩⟩

@[simp]
/-
**IsLprojection.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
/-
**IsLprojection.Subtype.boundedOrder** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.Su
btype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] →         [inst_2 : _root_.Module M X] → [inst_3 : Faithfu
lSMul M X] → BoundedOrder { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.boundedOrder [FaithfulSMul M X] :
    BoundedOrder { P : M // IsLprojection X P } where
  top := 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]
/-
**IsLprojection.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_bot [FaithfulSMul M X] : ↑(BoundedOrder.toOrderBot.toBot.bot : { P : M
 // IsLprojection X P }) = (0 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderBot.toBot.bot : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl

@[simp]
/-
**IsLprojection.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：coe_top [FaithfulSMul M X] : ↑(BoundedOrder.toOrderTop.toTop.top : { P : M
 // IsLprojection X P }) = (1 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderTop.toTop.top : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
/-
**IsLprojection.compl_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑Pᶜ * Q = Q - ↑P 
* Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLprojection.coe_compl`：coe_compl (P : { P : M // IsLprojection X P }) 
: ↑Pᶜ = (1 : M) - ↑P
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑Pᶜ * Q = Q - ↑P * Q := by
  rw [coe_compl, sub_mul, one_mul]
/-
**IsLprojection.mul_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑Pᶜ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLprojection.coe_compl`：coe_compl (P : { P : M // IsLprojection X P }) 
: ↑Pᶜ = (1 : M) - ↑P
· 使用引理 `IsIdempotentElem.mul_one_sub_self`：mul_one_sub_self (h : IsIdempotentEle
m a) : a * (1 - a) = 0
· 使用定理 `IsLprojection.proj`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : 
Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojectio
n X P → …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑Pᶜ = 0 := by
  rw [coe_compl, P.prop.proj.mul_one_sub_self]
/-
**IsLprojection.distrib_lattice_lemma** 是 Mathlib 中的一个定理，位于命名空间 `IsLprojection`。
形式化陈述：distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection
 X P }} : ((↑P : M) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = ↑P + ↑Q * ↑R * ↑Pᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLprojection.coe_inf`：coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLp
rojection X P }) : ↑(P ⊓ Q) = (↑P : M) * ↑Q
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsLprojection.commute`：commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLpro
jection X P) (h₂ : IsLprojection X Q) : Commute P Q
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsLprojection.mul_compl_self`：mul_compl_self {P : { P : M // IsLprojecti
on X P }} : (↑P : M) * ↑Pᶜ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `IsLprojection.proj`：∀ {X : Type u_1} [inst : NormedAddCommGroup X] {M : 
Type u_2} [inst_1 : Ring M] [inst_2 : _root_.Module M X] {P : M},   IsLprojectio
n X P → …
-/
theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }} :
    ((↑P : M) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = ↑P + ↑Q * ↑R * ↑Pᶜ := by
  rw [add_mul, mul_add, mul_add, (mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ)),
    ← mul_assoc (R : M) (↑Q * ↑R) _, ← coe_inf Q, (Pᶜ.prop.commute R.prop).eq,
    ((Q ⊓ R).prop.commute Pᶜ.prop).eq, (R.prop.commute (Q ⊓ R).prop).eq, coe_inf Q,
    mul_assoc (Q : M), ← mul_assoc, mul_assoc (R : M), (Pᶜ.prop.commute P.prop).eq, mul_compl_self,
    zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc, P.prop.proj.eq,
    R.prop.proj.eq, ← coe_inf Q, mul_assoc, ((Q ⊓ R).prop.commute Pᶜ.prop).eq, ← mul_assoc,
    Pᶜ.prop.proj.eq]

/-- This instance was created as an auxiliary definition when defining `Subtype.distribLattice`
all at once would cause a timeout. That is no longer the case. Keeping this as a useful shortcut.
-/
/-
**IsLprojection.** 是 Mathlib 中的一个实例，位于命名空间 `IsLprojection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance was created as an auxiliary definition when defining `Subtype.dist
ribLattice`
all at once would cause a timeout. That is no longer the case. Keeping this as a
 useful shortcut.
-/
instance [FaithfulSMul M X] : Lattice { P : M // IsLprojection X P } where
  sup := max
  inf := min
  le_sup_left P Q := by
    rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, ← mul_assoc, P.prop.proj.eq,
      sub_self, add_zero]
  le_sup_right P Q := by
    rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, (P.prop.commute Q.prop).eq,
      ← mul_assoc, Q.prop.proj.eq, add_sub_cancel]
  sup_le P Q R := by
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_sup, coe_inf, coe_sup, ← add_sub, add_mul,
      sub_mul, mul_assoc]
    intro h₁ h₂
    rw [← h₂, ← h₁]
  inf_le_left P Q := by
    rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, (Q.prop.commute P.prop).eq, ← mul_assoc,
      P.prop.proj.eq]
  inf_le_right P Q := by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq]
  le_inf P Q R := by
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_inf, coe_inf, ← mul_assoc]
    intro h₁ h₂
    rw [← h₁, ← h₂]
/-
**IsLprojection.Subtype.distribLattice** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.
Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → Dist
ribLattice { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.distribLattice [FaithfulSMul M X] :
    DistribLattice { P : M // IsLprojection X P } where
  le_sup_inf P Q R := by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, ← add_sub, ← add_sub, ← compl_mul, ← compl_mul, add_mul,
        mul_add, (Pᶜ.prop.commute Q.prop).eq, mul_add, ← mul_assoc, mul_assoc (Q : M),
        (Pᶜ.prop.commute P.prop).eq, mul_compl_self, zero_mul, mul_zero,
        zero_add, add_zero, ← mul_assoc, mul_assoc (Q : M), P.prop.proj.eq, Pᶜ.prop.proj.eq,
        mul_assoc, (Pᶜ.prop.commute R.prop).eq, ← mul_assoc]
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = (P : M) + ↑Q * ↑R * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, ← compl_mul, ←
        compl_mul, ← compl_mul, (Pᶜ.prop.commute (Q ⊓ R).prop).eq, coe_inf, mul_assoc,
        distrib_lattice_lemma, (Q.prop.commute R.prop).eq, distrib_lattice_lemma]
    rw [le_def, e₁, coe_inf, e₂]
/-
**IsLprojection.Subtype.BooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `IsLprojection.
Subtype`。
形式化陈述：{X : Type u_1} →   [inst : NormedAddCommGroup X] →     {M : Type u_2} →   
    [inst_1 : Ring M] → [inst_2 : _root_.Module M X] → [FaithfulSMul M X] → Bool
eanAlgebra { P // IsLprojection X P }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.BooleanAlgebra [FaithfulSMul M X] :
    BooleanAlgebra { P : M // IsLprojection X P } :=
  { IsLprojection.Subtype.instCompl,
    IsLprojection.Subtype.sdiff,
    IsLprojection.Subtype.boundedOrder with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
        (by
          rw [coe_top, coe_sup, coe_compl, add_sub_cancel, ← coe_compl, mul_compl_self,
            sub_zero])).le
    sdiff_eq := fun P Q => Subtype.ext <| by rw [coe_sdiff, ← coe_compl, coe_inf] }

end IsLprojection

