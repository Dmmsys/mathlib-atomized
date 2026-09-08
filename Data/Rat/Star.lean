/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Star ordered ring structures on `ℚ` and `ℚ≥0`

This file shows that `ℚ` and `ℚ≥0` are `StarOrderedRing`s. In particular, this means that every
nonnegative rational number is a sum of squares.
-/

public section

open AddSubmonoid Set
open scoped NNRat

namespace NNRat

/-
**NNRat.addSubmonoid_closure_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → AddSubmonoid.closure (Set.range fun x => x ^ n) = ⊤
参数：Set.range fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.eq_top_iff'`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : 
AddSubmonoid M), S = ⊤ ↔ ∀ (x : M), x ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `pow_sub₀`：pow_sub₀ (a : G₀) (ha : a != 0) (h : n <= m) : a ^ (m - n) = a
 ^ m * (a ^ n)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `NNRat.num_div_den`：num_div_den (q : Rat>=0) : (q.num : Rat>=0) / q.den =
 q
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) :
    closure (range fun x : ℚ≥0 ↦ x ^ n) = ⊤ := by
  refine (eq_top_iff' _).2 fun x ↦ ?_
  suffices x = (x.num * x.den ^ (n - 1)) • (x.den : ℚ≥0)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc, pow_sub₀, pow_one, mul_right_comm, ← mul_pow, mul_inv_cancel₀, one_pow, one_mul,
    ← div_eq_mul_inv, num_div_den]
  all_goals simp [x.den_pos.ne', Nat.one_le_iff_ne_zero, *]
/-
**NNRat.addSubmonoid_closure_range_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：AddSubmonoid.closure (Set.range fun x => x * x) = ⊤
参数：Set.range fun x => x * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `NNRat.addSubmonoid_closure_range_pow`：∀ {n : ℕ}, n ≠ 0 → AddSubmonoid.cl
osure (Set.range fun x => x ^ n) = ⊤
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ≥0 ↦ x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero
/-
**NNRat.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instStarOrderedRing : StarOrderedRing Rat>=0 where le_iff a b
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_nonneg_add`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1
 : Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftMono α]   [AddLeftReflectLE α
], a ≤ b ↔ ∃ c…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `NNRat.addSubmonoid_closure_range_mul_self`：AddSubmonoid.closure (Set.ran
ge fun x => x * x) = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance instStarOrderedRing : StarOrderedRing ℚ≥0 where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end NNRat

namespace Rat

/-
**Rat.addSubmonoid_closure_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → Even n → AddSubmonoid.closure (Set.range fun x => x ^ n
) = AddSubmonoid.nonneg ℚ
参数：Set.range fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Even.pow_abs`：Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `eq_nnratCast`：eq_nnratCast [DivisionSemiring α] [FunLike F Rat>=0 α] [Ri
ngHomClass F Rat>=0 α] (f : F) (q : Rat>=0) : f q = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `AddSubmonoid.ext`：∀ {M : Type u_1} [inst : AddZeroClass M] {S T : AddSub
monoid M}, (∀ (x : M), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `AddSubmonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : Add
ZeroClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N]
 [mc : AddMonoidH…
· 使用定理 `NNRat.addSubmonoid_closure_range_pow`：∀ {n : ℕ}, n ≠ 0 → AddSubmonoid.cl
osure (Set.range fun x => x ^ n) = ⊤
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AddMonoidHom.map_mclosure`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZe
roClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [
mc : AddMonoidH…
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  convert! (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x ↦ x ^ n).symm
  · have (x : ℚ) : ∃ y : ℚ≥0, y ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp [subset_antisymm_iff, range_subset_iff, this]
  · ext
    simp [NNRat.addSubmonoid_closure_range_pow hn₀, NNRat.exists]

@[simp]
/-
**Rat.addSubmonoid_closure_range_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：addSubmonoid_closure_range_mul_self : closure (range fun x : Rat => x * x)
 = nonneg _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Rat.addSubmonoid_closure_range_pow`：∀ {n : ℕ}, n ≠ 0 → Even n → AddSubmo
noid.closure (Set.range fun x => x ^ n) = AddSubmonoid.nonneg ℚ
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
-/
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two
/-
**Rat.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instStarOrderedRing : StarOrderedRing Rat where le_iff a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_nonneg_add`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1
 : Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftMono α]   [AddLeftReflectLE α
], a ≤ b ↔ ∃ c…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用引理 `Rat.addSubmonoid_closure_range_mul_self`：addSubmonoid_closure_range_mul_
self : closure (range fun x : Rat => x * x) = nonneg _
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Rat

