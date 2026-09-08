/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordinal arithmetic with cardinals

This file collects results about the cardinality of different ordinal operations.
-/

public section

universe u v
open Cardinal Ordinal Set

/-! ### Cardinal operations with ordinal indices -/

namespace Cardinal

/-- Bounds the cardinal of an ordinal-indexed union of sets. -/
/-
**Cardinal.mk_biUnion_le_of_le_lift** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_biUnion_le_of_le_lift {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
 (ho : lift.{v} o.card <= lift.{u} c) (hc : ℵ₀ <= c) (A : Ordinal -> Set β) (hA 
: forall j < o, #(A j) <= c) : #(⋃ j < o, A j) <= c
参数：ho : lift.{v} o.card <= lift.{u} c；hc : ℵ₀ <= c；A : Ordinal -> Set β；hA : for
all j < o, #(A j) <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_iUnion_le_lift`：mk_iUnion_le_lift {α : Type u} {ι : Type v} 
(f : ι -> Set α) : lift.{v} #(⋃ i, f i) <= lift.{u} #ι * ⨆ i, lift.{v} #(f i)
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c

--- 原说明 ---
Bounds the cardinal of an ordinal-indexed union of sets.
-/
lemma mk_biUnion_le_of_le_lift {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : lift.{v} o.card ≤ lift.{u} c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.prop

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_lift_le_of_le := mk_biUnion_le_of_le_lift
/-
**Cardinal.mk_biUnion_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_biUnion_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal} (ho : o.card 
<= c) (hc : ℵ₀ <= c) (A : Ordinal -> Set β) (hA : forall j < o, #(A j) <= c) : #
(⋃ j < o, A j) <= c
参数：ho : o.card <= c；hc : ℵ₀ <= c；A : Ordinal -> Set β；hA : forall j < o, #(A j) 
<= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.mk_biUnion_le_of_le_lift`：mk_biUnion_le_of_le_lift {β : Type v}
 {o : Ordinal.{u}} {c : Cardinal.{v}} (ho : lift.{v} o.card <= lift.{u} c) (hc :
 ℵ₀ <= c) (A : Ordinal …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
lemma mk_biUnion_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal}
    (ho : o.card ≤ c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by
  apply mk_biUnion_le_of_le_lift _ hc A hA
  rwa [Cardinal.lift_le]

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_le_of_le := mk_biUnion_le_of_le

end Cardinal

/-! ### Cardinality of ordinals -/

namespace Ordinal

/-
**Ordinal.lift_card_iSup_le_sum_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_card_iSup_le_sum_card {ι : Type u} (f : ι -> Ordinal.{v}) : Cardinal.
lift.{u} (⨆ i, f i).card <= Cardinal.sum fun i => (f i).card
参数：f : ι -> Ordinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Ordinal.card_zero`：card_zero : card 0 = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_surjective`：lift_mk_le_lift_mk_of_surject
ive {α : Type u} {β : Type v} {f : α -> β} (hf : Surjective f) : Cardinal.lift.{
u} (#β) <= Cardinal.lift.{v} (#…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `EquivLike.comp_surjective`：comp_surjective (f : α -> β) (e : F) : Functi
on.Surjective (e ∘ f) ↔ Function.Surjective f
· 使用定理 `lt_ciSup_iff'`：lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a <
 iSup f ↔ exists i, a < f i
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_card_iSup_le_sum_card {ι : Type u} (f : ι → Ordinal.{v}) :
    Cardinal.lift.{u} (⨆ i, f i).card ≤ Cardinal.sum fun i ↦ (f i).card := by
  by_cases! hf : ¬ BddAbove (range f)
  · simp [ciSup_of_not_bddAbove hf]
  simp_rw [← mk_toType]
  rw [← mk_sigma, ← Cardinal.lift_id'.{v} #(Σ _, _), ← Cardinal.lift_umax.{v, u}]
  apply lift_mk_le_lift_mk_of_surjective (f := .mk ∘ (⟨·.2.toOrd,
    (mem_Iio.mp (ToType.toOrd _).2).trans_le (le_ciSup hf _)⟩))
  rw [EquivLike.comp_surjective]
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := (lt_ciSup_iff' hf).mp hx
  exact ⟨⟨i, .mk ⟨x, hi⟩⟩, by simp⟩
/-
**Ordinal.card_iSup_le_sum_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_le_sum_card {ι : Type u} (f : ι -> Ordinal.{max u v}) : (⨆ i, f 
i).card <= Cardinal.sum fun i => (f i).card
参数：f : ι -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_card_iSup_le_sum_card`：lift_card_iSup_le_sum_card {ι : Type
 u} (f : ι -> Ordinal.{v}) : Cardinal.lift.{u} (⨆ i, f i).card <= Cardinal.sum f
un i => (f i).card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem card_iSup_le_sum_card {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (⨆ i, f i).card ≤ Cardinal.sum fun i ↦ (f i).card := by
  have := lift_card_iSup_le_sum_card f
  rwa [Cardinal.lift_id'] at this
/-
**Ordinal.card_iSup_Iio_le_sum_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_Iio_le_sum_card {o : Ordinal.{u}} (f : Iio o -> Ordinal.{max u v
}) : (⨆ a : Iio o, f a).card <= Cardinal.sum fun i : o.ToType => (f i.toOrd).car
d
参数：f : Iio o -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `Ordinal.card_iSup_le_sum_card`：card_iSup_le_sum_card {ι : Type u} (f : ι
 -> Ordinal.{max u v}) : (⨆ i, f i).card <= Cardinal.sum fun i => (f i).card
-/
theorem card_iSup_Iio_le_sum_card {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.sum fun i : o.ToType ↦ (f i.toOrd).card := by
  apply le_of_eq_of_le (congr_arg _ _).symm (card_iSup_le_sum_card _)
  simpa using ToType.mk.symm.iSup_comp (g := fun x ↦ f x)
/-
**Ordinal.card_iSup_Iio_le_card_mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_Iio_le_card_mul_iSup {o : Ordinal.{u}} (f : Iio o -> Ordinal.{ma
x u v}) : (⨆ a : Iio o, f a).card <= Cardinal.lift.{v} o.card * ⨆ a : Iio o, (f 
a).card
参数：f : Iio o -> Ordinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.card_iSup_Iio_le_sum_card`：card_iSup_Iio_le_sum_card {o : Ordina
l.{u}} (f : Iio o -> Ordinal.{max u v}) : (⨆ a : Iio o, f a).card <= Cardinal.su
m fun i : o.ToType => (…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup`：sum_le_lift_mk_mul_iSup {ι : Type u} (
f : ι -> Cardinal.{max u v}) : sum f <= lift #ι * ⨆ i, f i
-/
theorem card_iSup_Iio_le_card_mul_iSup {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.lift.{v} o.card * ⨆ a : Iio o, (f a).card := by
  apply (card_iSup_Iio_le_sum_card f).trans
  convert! ← sum_le_lift_mk_mul_iSup _
  · exact mk_toType o
  · exact ToType.mk.symm.iSup_comp (g := fun x ↦ (f x).card)
/-
**Ordinal.card_iSup_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_le_lift {ι : Type u} {c : Cardinal} {f : ι -> Ordinal.{v}} (hι :
 Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c) (hf : forall i, (f i).card <= c) :
 (⨆ i, f i).card <= c
参数：hι : Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c；hf : forall i, (f i).card <=
 c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.card_le_nat`：card_le_nat {o} {n : Nat} : card o <= n ↔ o <= n
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.lift_card_iSup_le_sum_card`：lift_card_iSup_le_sum_card {ι : Type
 u} (f : ι -> Ordinal.{v}) : Cardinal.lift.{u} (⨆ i, f i).card <= Cardinal.sum f
un i => (f i).card
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup_lift`：sum_le_lift_mk_mul_iSup_lift {ι :
 Type u} (f : ι -> Cardinal.{v}) : sum f <= lift #ι * ⨆ i, lift (f i)
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem card_iSup_le_lift {ι : Type u} {c : Cardinal} {f : ι → Ordinal.{v}}
    (hι : Cardinal.lift.{v} #ι ≤ Cardinal.lift.{u} c) (hf : ∀ i, (f i).card ≤ c) :
    (⨆ i, f i).card ≤ c := by
  by_cases! hc : c < ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    rw [card_le_nat]
    refine ciSup_le' fun i ↦ ?_
    simpa using hf i
  · rw [← Cardinal.lift_le.{u}]
    apply (lift_card_iSup_le_sum_card ..).trans ((sum_le_lift_mk_mul_iSup_lift _).trans _)
    rw [← mul_eq_self hc, Cardinal.lift_mul]
    apply mul_le_mul' hι (ciSup_le' _)
    simpa [← lift_card]
/-
**Ordinal.card_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_le {ι : Type*} {c : Cardinal} {f : ι -> Ordinal} (hι : #ι <= c) 
(hf : forall i, (f i).card <= c) : (⨆ i, f i).card <= c
参数：hι : #ι <= c；hf : forall i, (f i).card <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_iSup_le_lift`：card_iSup_le_lift {ι : Type u} {c : Cardinal}
 {f : ι -> Ordinal.{v}} (hι : Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c) (hf :
 forall i, (f i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem card_iSup_le {ι : Type*} {c : Cardinal} {f : ι → Ordinal}
    (hι : #ι ≤ c) (hf : ∀ i, (f i).card ≤ c) : (⨆ i, f i).card ≤ c := by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_le_lift hι hf
/-
**Ordinal.card_iSup_Iio_le_of_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_Iio_le_of_lift {o : Ordinal.{u}} {c : Cardinal} {f : Iio o -> Or
dinal.{v}} (hι : Cardinal.lift.{v} o.card <= Cardinal.lift.{u} c) (hf : forall i
, (f i).card <= c) : (⨆ i, f i).card <= c
参数：hι : Cardinal.lift.{v} o.card <= Cardinal.lift.{u} c；hf : forall i, (f i).car
d <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_iSup_le_lift`：card_iSup_le_lift {ι : Type u} {c : Cardinal}
 {f : ι -> Ordinal.{v}} (hι : Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c) (hf :
 forall i, (f i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem card_iSup_Iio_le_of_lift {o : Ordinal.{u}} {c : Cardinal} {f : Iio o → Ordinal.{v}}
    (hι : Cardinal.lift.{v} o.card ≤ Cardinal.lift.{u} c) (hf : ∀ i, (f i).card ≤ c) :
    (⨆ i, f i).card ≤ c := by
  apply card_iSup_le_lift _ hf
  conv_rhs => rw [← Cardinal.lift_lift.{u, u + 1}]
  rwa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, ← Cardinal.lift_lift.{v, u + 1},
    Cardinal.lift_le]
/-
**Ordinal.card_iSup_Iio_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_iSup_Iio_le {o : Ordinal} {c : Cardinal} {f : Iio o -> Ordinal} (hι :
 o.card <= c) (hf : forall i, (f i).card <= c) : (⨆ i, f i).card <= c
参数：hι : o.card <= c；hf : forall i, (f i).card <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_iSup_Iio_le_of_lift`：card_iSup_Iio_le_of_lift {o : Ordinal.
{u}} {c : Cardinal} {f : Iio o -> Ordinal.{v}} (hι : Cardinal.lift.{v} o.card <=
 Cardinal.lift.{u} c) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem card_iSup_Iio_le {o : Ordinal} {c : Cardinal} {f : Iio o → Ordinal}
    (hι : o.card ≤ c) (hf : ∀ i, (f i).card ≤ c) : (⨆ i, f i).card ≤ c := by
  rw [← Cardinal.lift_le] at hι
  simpa using card_iSup_Iio_le_of_lift hι hf
/-
**Ordinal.card_sSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_sSup_le {c : Cardinal} {s : Set Ordinal.{u}} (hs : #s <= Cardinal.lif
t.{u + 1} c) (hs' : forall x in s, x.card <= c) : (sSup s).card <= c
参数：hs : #s <= Cardinal.lift.{u + 1} c；hs' : forall x in s, x.card <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Ordinal.card_iSup_le_lift`：card_iSup_le_lift {ι : Type u} {c : Cardinal}
 {f : ι -> Ordinal.{v}} (hι : Cardinal.lift.{v} #ι <= Cardinal.lift.{u} c) (hf :
 forall i, (f i…
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem card_sSup_le {c : Cardinal} {s : Set Ordinal.{u}}
    (hs : #s ≤ Cardinal.lift.{u + 1} c) (hs' : ∀ x ∈ s, x.card ≤ c) : (sSup s).card ≤ c := by
  rw [sSup_eq_iSup']
  apply card_iSup_le_lift
  · rwa [Cardinal.lift_id'.{u, u + 1}]
  · simpa
/-
**Ordinal.card_opow_le_of_omega0_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_le_of_omega0_le_left {a : Ordinal} (ha : ω <= a) (b : Ordinal) :
 (a ^ b).card <= max a.card b.card
参数：ha : ω <= a；b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
· 使用定理 `Ordinal.card_zero`：card_zero : card 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `Ordinal.card_mul`：card_mul (a b) : card (a * b) = card a * card b
· 使用定理 `Ordinal.card_add_one`：card_add_one (o : Ordinal) : card (o + 1) = card o
 + 1
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_right`：mul_eq_max_of_aleph0_le_right {a
 b : Cardinal} (h' : a != 0) (h : ℵ₀ <= b) : a * b = max a b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ordinal.card_eq_zero`：card_eq_zero {o} : card o = 0 ↔ o = 0
· 使用定理 `Ordinal.opow_eq_zero`：opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧
 b != 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.aleph0_le_card`：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `max_assoc`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max (max
 a b) c = max a (max b c)
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
（共 38 条，此处仅展示前 30 条）
-/
theorem card_opow_le_of_omega0_le_left {a : Ordinal} (ha : ω ≤ a) (b : Ordinal) :
    (a ^ b).card ≤ max a.card b.card := by
  induction b using limitRecOn with
  | zero => simpa using one_lt_omega0.le.trans ha
  | add_one b IH =>
    rw [opow_add_one, card_mul, card_add_one, Cardinal.mul_eq_max_of_aleph0_le_right, max_comm]
    · grw [IH]
      rw [← max_assoc, max_self]
      grw [← le_self_add]
    · rw [ne_eq, card_eq_zero, opow_eq_zero]
      rintro ⟨rfl, -⟩
      cases omega0_pos.not_ge ha
    · rwa [aleph0_le_card]
  | limit b hb IH =>
    rw [(isNormal_opow (one_lt_omega0.trans_le ha)).apply_of_isSuccLimit hb]
    exact card_iSup_Iio_le (le_max_right ..) fun i ↦
      (IH i i.2).trans (max_le_max_left _ (card_le_card i.2.le))
/-
**Ordinal.card_opow_le_of_omega0_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω <= b) 
: (a ^ b).card <= max a.card b.card
参数：a : Ordinal；hb : ω <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.eq_natCast_or_omega0_le`：eq_natCast_or_omega0_le (o : Ordinal) :
 (exists n : Nat, o = n) ∨ ω <= o
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `Ordinal.opow_le_opow_left`：opow_le_opow_left {a b : Ordinal} (c : Ordina
l) (ab : a <= b) : a ^ c <= b ^ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Ordinal.card_opow_le_of_omega0_le_left`：card_opow_le_of_omega0_le_left {
a : Ordinal} (ha : ω <= a) (b : Ordinal) : (a ^ b).card <= max a.card b.card
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω ≤ b) :
    (a ^ b).card ≤ max a.card b.card := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (natCast_lt_omega0 n).le).trans
    apply (card_opow_le_of_omega0_le_left le_rfl _).trans
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b
/-
**Ordinal.card_opow_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_le (a b : Ordinal) : (a ^ b).card <= max ℵ₀ (max a.card b.card)
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.eq_natCast_or_omega0_le`：eq_natCast_or_omega0_le (o : Ordinal) :
 (exists n : Nat, o = n) ∨ ω <= o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.card_opow_le_of_omega0_le_right`：card_opow_le_of_omega0_le_right
 (a : Ordinal) {b : Ordinal} (hb : ω <= b) : (a ^ b).card <= max a.card b.card
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Ordinal.card_opow_le_of_omega0_le_left`：card_opow_le_of_omega0_le_left {
a : Ordinal} (ha : ω <= a) (b : Ordinal) : (a ^ b).card <= max a.card b.card
-/
theorem card_opow_le (a b : Ordinal) : (a ^ b).card ≤ max ℵ₀ (max a.card b.card) := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · obtain ⟨m, rfl⟩ | hb := eq_natCast_or_omega0_le b
    · rw [opow_natCast, ← natCast_pow, card_nat]
      exact le_max_of_le_left natCast_le_aleph0
    · exact (card_opow_le_of_omega0_le_right _ hb).trans (le_max_right _ _)
  · exact (card_opow_le_of_omega0_le_left ha _).trans (le_max_right _ _)
/-
**Ordinal.card_opow_eq_of_omega0_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω <= a) (hb : 0 < b) 
: (a ^ b).card = max a.card b.card
参数：ha : ω <= a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.card_opow_le_of_omega0_le_left`：card_opow_le_of_omega0_le_left {
a : Ordinal} (ha : ω <= a) (b : Ordinal) : (a ^ b).card <= max a.card b.card
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `Ordinal.left_le_opow`：left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 <
 b) : a <= a ^ b
· 使用定理 `Ordinal.right_le_opow`：right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1
 < a) : b <= a ^ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω ≤ a) (hb : 0 < b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)
/-
**Ordinal.card_opow_eq_of_omega0_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω <= b)
 : (a ^ b).card = max a.card b.card
参数：ha : 1 < a；hb : ω <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.card_opow_le_of_omega0_le_right`：card_opow_le_of_omega0_le_right
 (a : Ordinal) {b : Ordinal} (hb : ω <= b) : (a ^ b).card <= max a.card b.card
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `Ordinal.left_le_opow`：left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 <
 b) : a <= a ^ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `Ordinal.right_le_opow`：right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1
 < a) : b <= a ^ b
-/
theorem card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω ≤ b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha
/-
**Ordinal.card_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_omega0_opow {a : Ordinal} (h : a != 0) : card (ω ^ a) = max ℵ₀ a.card
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.card_opow_eq_of_omega0_le_left`：card_opow_eq_of_omega0_le_left {
a b : Ordinal} (ha : ω <= a) (hb : 0 < b) : (a ^ b).card = max a.card b.card
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Ordinal.card_omega0`：card_omega0 : card ω = ℵ₀
-/
theorem card_omega0_opow {a : Ordinal} (h : a ≠ 0) : card (ω ^ a) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt, card_omega0]
/-
**Ordinal.card_opow_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card
参数：h : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.card_opow_eq_of_omega0_le_right`：card_opow_eq_of_omega0_le_right
 {a b : Ordinal} (ha : 1 < a) (hb : ω <= b) : (a ^ b).card = max a.card b.card
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ordinal.card_omega0`：card_omega0 : card ω = ℵ₀
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
theorem card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_right h le_rfl, card_omega0, max_comm]
/-
**Ordinal.isPrincipal_opow_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_opow_omega (o : Ordinal) : IsPrincipal (· ^ ·) (ω_ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.omega_zero`：omega_zero : ω_ 0 = ω
· 使用定理 `Ordinal.isPrincipal_opow_omega0`：isPrincipal_opow_omega0 : IsPrincipal (
· ^ ·) ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lt_omega_iff_card_lt`：lt_omega_iff_card_lt {x o : Ordinal} : x 
< ω_ o ↔ x.card < ℵ_ o
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.card_opow_le`：card_opow_le (a b : Ordinal) : (a ^ b).card <= max
 ℵ₀ (max a.card b.card)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Cardinal.aleph_zero`：aleph_zero : ℵ_ 0 = ℵ₀
· 使用定理 `Cardinal.aleph_lt_aleph`：aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o
₂ ↔ o₁ < o₂
-/
theorem isPrincipal_opow_omega (o : Ordinal) : IsPrincipal (· ^ ·) (ω_ o) := by
  obtain rfl | ho := eq_zero_or_pos o
  · rw [omega_zero]
    exact isPrincipal_opow_omega0
  · intro a b ha hb
    rw [lt_omega_iff_card_lt] at ha hb ⊢
    apply (card_opow_le a b).trans_lt (max_lt _ (max_lt ha hb))
    rwa [← aleph_zero, aleph_lt_aleph]

@[deprecated (since := "2026-03-18")] alias principal_opow_omega := isPrincipal_opow_omega
/-
**Ordinal.IsInitial.isPrincipal_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitia
l`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o.IsInitial → Ordinal.omega0 ≤ o → Ordinal.IsPrinci
pal (fun x1 x2 => x1 ^ x2) o
参数：fun x1 x2 => x1 ^ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.mem_range_omega_iff`：mem_range_omega_iff {x : Ordinal} : x in ra
nge omega ↔ ω <= x ∧ IsInitial x
· 使用定理 `Ordinal.isPrincipal_opow_omega`：isPrincipal_opow_omega (o : Ordinal) : I
sPrincipal (· ^ ·) (ω_ o)
-/
theorem IsInitial.isPrincipal_opow {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· ^ ·) o := by
  obtain ⟨a, rfl⟩ := mem_range_omega_iff.2 ⟨ho, h⟩
  exact isPrincipal_opow_omega a

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_opow := IsInitial.isPrincipal_opow
/-
**Ordinal.isPrincipal_opow_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_opow_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· ^ ·) c
.ord
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsInitial.isPrincipal_opow`：∀ {o : Ordinal.{u_1}}, o.IsInitial →
 Ordinal.omega0 ≤ o → Ordinal.IsPrincipal (fun x1 x2 => x1 ^ x2) o
· 使用定理 `Ordinal.isInitial_ord`：isInitial_ord (c : Cardinal) : IsInitial c.ord
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.omega0_le_ord`：omega0_le_ord {a : Cardinal} : ω <= a.ord ↔ ℵ₀ <
= a
-/
theorem isPrincipal_opow_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· ^ ·) c.ord := by
  apply (isInitial_ord c).isPrincipal_opow
  rwa [omega0_le_ord]

@[deprecated (since := "2026-03-18")] alias principal_opow_ord := isPrincipal_opow_ord

/-! ### Initial ordinals are principal -/

/-
**Ordinal.isPrincipal_add_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· + ·) c.
ord
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c

--- 原说明 ---
### Initial ordinals are principal
-/
theorem isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· + ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_add] at *
  exact add_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord
/-
**Ordinal.IsInitial.isPrincipal_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitial
`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o.IsInitial → Ordinal.omega0 ≤ o → Ordinal.IsPrinci
pal (fun x1 x2 => x1 + x2) o
参数：fun x1 x2 => x1 + x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsInitial.ord_card`：∀ {o : Ordinal.{u_1}}, o.IsInitial → o.card.
ord = o
· 使用定理 `Ordinal.isPrincipal_add_ord`：isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀
 <= c) : IsPrincipal (· + ·) c.ord
· 使用定理 `Ordinal.aleph0_le_card`：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
-/
theorem IsInitial.isPrincipal_add {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· + ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_add_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_add := IsInitial.isPrincipal_add
/-
**Ordinal.isPrincipal_add_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_add_omega (o : Ordinal) : IsPrincipal (· + ·) (ω_ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsInitial.isPrincipal_add`：∀ {o : Ordinal.{u_1}}, o.IsInitial → 
Ordinal.omega0 ≤ o → Ordinal.IsPrincipal (fun x1 x2 => x1 + x2) o
· 使用定理 `Ordinal.isInitial_omega`：isInitial_omega (o : Ordinal) : IsInitial (omeg
a o)
· 使用定理 `Ordinal.omega0_le_omega`：omega0_le_omega (o : Ordinal) : ω <= ω_ o
-/
theorem isPrincipal_add_omega (o : Ordinal) : IsPrincipal (· + ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_add (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_add_omega := isPrincipal_add_omega
/-
**Ordinal.isPrincipal_mul_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_ord {c : Cardinal} (hc : ℵ₀ <= c) : IsPrincipal (· * ·) c.
ord
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Ordinal.card_mul`：card_mul (a b) : card (a * b) = card a * card b
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c
-/
theorem isPrincipal_mul_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· * ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_mul] at *
  exact mul_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_mul_ord := isPrincipal_mul_ord
/-
**Ordinal.IsInitial.isPrincipal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsInitial
`。
形式化陈述：∀ {o : Ordinal.{u_1}}, o.IsInitial → Ordinal.omega0 ≤ o → Ordinal.IsPrinci
pal (fun x1 x2 => x1 * x2) o
参数：fun x1 x2 => x1 * x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.IsInitial.ord_card`：∀ {o : Ordinal.{u_1}}, o.IsInitial → o.card.
ord = o
· 使用定理 `Ordinal.isPrincipal_mul_ord`：isPrincipal_mul_ord {c : Cardinal} (hc : ℵ₀
 <= c) : IsPrincipal (· * ·) c.ord
· 使用定理 `Ordinal.aleph0_le_card`：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
-/
theorem IsInitial.isPrincipal_mul {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· * ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_mul_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_mul := IsInitial.isPrincipal_mul
/-
**Ordinal.isPrincipal_mul_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isPrincipal_mul_omega (o : Ordinal) : IsPrincipal (· * ·) (ω_ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsInitial.isPrincipal_mul`：∀ {o : Ordinal.{u_1}}, o.IsInitial → 
Ordinal.omega0 ≤ o → Ordinal.IsPrincipal (fun x1 x2 => x1 * x2) o
· 使用定理 `Ordinal.isInitial_omega`：isInitial_omega (o : Ordinal) : IsInitial (omeg
a o)
· 使用定理 `Ordinal.omega0_le_omega`：omega0_le_omega (o : Ordinal) : ω <= ω_ o
-/
theorem isPrincipal_mul_omega (o : Ordinal) : IsPrincipal (· * ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_mul (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_mul_omega := isPrincipal_mul_omega

end Ordinal

