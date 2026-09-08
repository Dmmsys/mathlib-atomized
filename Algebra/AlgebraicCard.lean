/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.RingTheory.Algebraic.Basic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `#R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `Liouville.transcendental`.
-/

public section


universe u v

open Cardinal Polynomial Set

open Cardinal Polynomial

namespace Algebraic

/-
**Algebraic.infinite_of_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [Ch
arZero A] : { x : A | IsAlgebraic R x }.Infinite
参数：R A : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionWithZero.nontrivial`：∀ (M₀ : Type u_2) (A : Type u_7) [inst : M
onoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A] [Nontrivial A],   N
ontrivial M₀
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Set.infinite_of_injective_forall_mem`：infinite_of_injective_forall_mem [
Infinite α] {s : Set β} {f : α -> β} (hi : Injective f) (hf : forall x : α, f x 
in s) : s.Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `isAlgebraic_natCast`：isAlgebraic_natCast [Nontrivial R] (n : Nat) : IsAl
gebraic R (n : A)
-/
theorem infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by
  let := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_natCast
/-
**Algebraic.aleph0_le_cardinalMk_of_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
c`。
形式化陈述：aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A] [Alge
bra R A] [CharZero A] : ℵ₀ <= #{ x : A // IsAlgebraic R x }
参数：R A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Algebraic.infinite_of_charZero`：infinite_of_charZero (R A : Type*) [Comm
Ring R] [Ring A] [Algebra R A] [CharZero A] : { x : A | IsAlgebraic R x }.Infini
te
-/
theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } :=
  infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)

section lift

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/-
**Algebraic.cardinalMk_lift_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_lift_le_mul : Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } <
= Cardinal.lift.{v} #R[X] * ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_uLift`：mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α
· 使用定理 `Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le`：lift_mk_le_lift_
mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal} (f : α ->
 β) (hf : forall b : β, lift.{v} #(f ⁻¹' {b}…
· 使用定理 `Cardinal.lift_le_aleph0`：lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c 
<= ℵ₀ ↔ c <= ℵ₀
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.MapsTo.countable_of_injOn`：∀ {α : Type u} {β : Type v} {s : Set α} {
t : Set β} {f : α → β},   Set.MapsTo f s t → Set.InjOn f s → t.Countable → s.Cou
ntable
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Polynomial.rootSet_finite`：rootSet_finite (p : T[X]) (S : Type*) [CommRi
ng S] [IsDomain S] [Algebra T S] : (p.rootSet S).Finite
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem cardinalMk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ Cardinal.lift.{v} #R[X] * ℵ₀ := by
  rw [← mk_uLift, ← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0, le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.countable_of_injOn Subtype.coe_injective.injOn (f.rootSet_finite A).countable
  rintro x (rfl : g x = f)
  exact mem_rootSet.2 ⟨hg₁ x, hg₂ x⟩
/-
**Algebraic.cardinalMk_lift_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_lift_le_max : Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } <
= max (Cardinal.lift.{v} #R) ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Algebraic.cardinalMk_lift_le_mul`：cardinalMk_lift_le_mul : Cardinal.lift
.{u} #{ x : A // IsAlgebraic R x } <= Cardinal.lift.{v} #R[X] * ℵ₀
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `Polynomial.cardinalMk_le_max`：cardinalMk_le_max {R : Type u} [Semiring R
] : #(R[X]) <= max #R ℵ₀
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.mul_aleph0_eq`：mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ <= a) : a 
* ℵ₀ = a
-/
theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ :=
  (cardinalMk_lift_le_mul R A).trans <| by grw [lift_le.2 cardinalMk_le_max]; simp

@[simp]
/-
**Algebraic.cardinalMk_lift_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_lift_of_infinite [Infinite R] : Cardinal.lift.{u} #{ x : A // I
sAlgebraic R x } = Cardinal.lift.{v} #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Algebraic.cardinalMk_lift_le_max`：cardinalMk_lift_le_max : Cardinal.lift
.{u} #{ x : A // IsAlgebraic R x } <= max (Cardinal.lift.{v} #R) ℵ₀
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `instInfiniteULift`：∀ {α : Type v} [Infinite α], Infinite (ULift.{u, v} α
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem cardinalMk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R :=
  ((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm <|
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

variable [Countable R]

@[simp]
/-
**Algebraic.countable** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：∀ (R : Type u) (A : Type v) [inst : CommRing R] [IsDomain R] [inst_2 : Com
mRing A] [IsDomain A] [inst_4 : Algebra R A]   [Module.IsTorsionFree R A] [Count
able R], {x | IsAlgebraic R x}.Countable
参数：R : Type u；A : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.lift_le_aleph0`：lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c 
<= ℵ₀ ↔ c <= ℵ₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Algebraic.cardinalMk_lift_le_max`：cardinalMk_lift_le_max : Cardinal.lift
.{u} #{ x : A // IsAlgebraic R x } <= max (Cardinal.lift.{v} #R) ℵ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
-/
protected theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

@[simp]
/-
**Algebraic.cardinalMk_of_countable_of_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raic`。
形式化陈述：cardinalMk_of_countable_of_charZero [CharZero A] : #{ x : A // IsAlgebraic
 R x } = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.Countable.le_aleph0`：∀ {α : Type u} {s : Set α}, s.Countable → Cardi
nal.mk ↑s ≤ Cardinal.aleph0
· 使用定理 `Algebraic.countable`：∀ (R : Type u) (A : Type v) [inst : CommRing R] [Is
Domain R] [inst_2 : CommRing A] [IsDomain A] [inst_4 : Algebra R A]   [Module.Is
TorsionFr…
· 使用定理 `Algebraic.aleph0_le_cardinalMk_of_charZero`：aleph0_le_cardinalMk_of_char
Zero (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [CharZero A] : ℵ₀ <= #{ x
 : A // IsAlgebraic R x }
-/
theorem cardinalMk_of_countable_of_charZero [CharZero A] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ :=
  (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinalMk_of_charZero R A)

end lift

section NonLift

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/-
**Algebraic.cardinalMk_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } <= #R[X] * ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebraic.cardinalMk_lift_le_mul`：cardinalMk_lift_le_mul : Cardinal.lift
.{u} #{ x : A // IsAlgebraic R x } <= Cardinal.lift.{v} #R[X] * ℵ₀
-/
theorem cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } ≤ #R[X] * ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R[X]]
  exact cardinalMk_lift_le_mul R A

@[stacks 09GK]
/-
**Algebraic.cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_le_max : #{ x : A // IsAlgebraic R x } <= max #R ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebraic.cardinalMk_lift_le_max`：cardinalMk_lift_le_max : Cardinal.lift
.{u} #{ x : A // IsAlgebraic R x } <= max (Cardinal.lift.{v} #R) ℵ₀
-/
theorem cardinalMk_le_max : #{ x : A // IsAlgebraic R x } ≤ max #R ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R]
  exact cardinalMk_lift_le_max R A

@[simp]
/-
**Algebraic.cardinalMk_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic`。
形式化陈述：cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Algebraic.cardinalMk_lift_of_infinite`：cardinalMk_lift_of_infinite [Infi
nite R] : Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R
-/
theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R :=
  lift_inj.1 <| cardinalMk_lift_of_infinite R A

end NonLift

end Algebraic

