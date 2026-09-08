/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!

# Cardinality of Ore localizations

This file contains some results on cardinality of Ore localizations.

## TODO

- Prove or disprove `OreLocalization.cardinalMk_le_lift_cardinalMk_of_commute`
  with `Commute` assumption removed.

-/

public section

universe u v

open Cardinal Function

namespace OreLocalization

variable {R : Type u} [Monoid R] (S : Submonoid R) [OreLocalization.OreSet S]
  (X : Type v) [MulAction R X]

@[to_additive]
/-
**OreLocalization.oreDiv_one_surjective_of_finite_left** 是 Mathlib 中的一个定理，位于命名空间
 `OreLocalization`。
形式化陈述：oreDiv_one_surjective_of_finite_left [Finite S] : Surjective (fun x => x /
ₒ (1 : ↥S) : X -> OreLocalization S X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Finite.exists_ne_map_eq_of_infinite`：Finite.exists_ne_map_eq_of_infinite
 {α β} [Infinite α] [Finite β] (f : α -> β) : exists x y : α, x != y ∧ f x = f y
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
-/
theorem oreDiv_one_surjective_of_finite_left [Finite S] :
    Surjective (fun x ↦ x /ₒ (1 : ↥S) : X → OreLocalization S X) := by
  refine OreLocalization.ind fun x s ↦ ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := ℕ) (s ^ ·)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1)).1, ?_, ?_⟩
  · change s ^ j • x = s ^ (j + 1) • s ^ (i - (j + 1)) • x
    rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hlt, heq]
  · simp_rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, mul_one, pow_succ]

@[to_additive]
/-
**OreLocalization.oreDiv_one_surjective_of_finite_right** 是 Mathlib 中的一个定理，位于命名空
间 `OreLocalization`。
形式化陈述：oreDiv_one_surjective_of_finite_right [Finite X] : Surjective (fun x => x 
/ₒ (1 : ↥S) : X -> OreLocalization S X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Finite.exists_ne_map_eq_of_infinite`：Finite.exists_ne_map_eq_of_infinite
 {α β} [Infinite α] [Finite β] (f : α -> β) : exists x y : α, x != y ∧ f x = f y
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
-/
theorem oreDiv_one_surjective_of_finite_right [Finite X] :
    Surjective (fun x ↦ x /ₒ (1 : ↥S) : X → OreLocalization S X) := by
  refine OreLocalization.ind fun x s ↦ ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := ℕ) (s ^ · • x)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1)).1, ?_, ?_⟩
  · change s ^ j • x = s ^ (j + 1) • s ^ (i - (j + 1)) • x
    rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hlt, heq]
  · simp_rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, mul_one, pow_succ]

@[to_additive]
/-
**OreLocalization.numeratorHom_surjective_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `O
reLocalization`。
形式化陈述：numeratorHom_surjective_of_finite [Finite S] : Surjective (numeratorHom (S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.oreDiv_one_surjective_of_finite_left`：oreDiv_one_surject
ive_of_finite_left [Finite S] : Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreLoc
alization S X)
-/
theorem numeratorHom_surjective_of_finite [Finite S] : Surjective (numeratorHom (S := S)) :=
  oreDiv_one_surjective_of_finite_left S R

@[to_additive]
/-
**OreLocalization.cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：cardinalMk_le_max : #(OreLocalization S X) <= max (lift.{v} #S) (lift.{u} 
#X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_surjective`：lift_mk_le_lift_mk_of_surject
ive {α : Type u} {β : Type v} {f : α -> β} (hf : Surjective f) : Cardinal.lift.{
u} (#β) <= Cardinal.lift.{v} (#…
· 使用定理 `OreLocalization.oreDiv_one_surjective_of_finite_right`：oreDiv_one_surjec
tive_of_finite_right [Finite X] : Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreL
ocalization S X)
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `OreLocalization.oreDiv_one_surjective_of_finite_left`：oreDiv_one_surject
ive_of_finite_left [Finite S] : Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreLoc
alization S X)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem cardinalMk_le_max : #(OreLocalization S X) ≤ max (lift.{v} #S) (lift.{u} #X) := by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rw [lift_umax.{v, u}, lift_id'] at this
    exact le_max_of_le_right this
  rcases finite_or_infinite S with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_left S X)
    rw [lift_umax.{v, u}, lift_id'] at this
    exact le_max_of_le_right this
  convert! ←
    mk_le_of_surjective (show Surjective fun x : X × S ↦ x.1 /ₒ x.2 from Quotient.mk''_surjective)
  rw [mk_prod, mul_comm]
  refine mul_eq_max ?_ ?_ <;> simp

@[to_additive]
/-
**OreLocalization.cardinalMk_le** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：cardinalMk_le : #(OreLocalization S R) <= #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OreLocalization.cardinalMk_le_max`：cardinalMk_le_max : #(OreLocalization
 S X) <= max (lift.{v} #S) (lift.{u} #X)
-/
theorem cardinalMk_le : #(OreLocalization S R) ≤ #R := by
  convert! ← cardinalMk_le_max S R
  simp_rw [lift_id, max_eq_right_iff, mk_subtype_le]

-- TODO: remove the `Commute` assumption
@[to_additive]
/-
**OreLocalization.cardinalMk_le_lift_cardinalMk_of_commute** 是 Mathlib 中的一个定理，位于
命名空间 `OreLocalization`。
形式化陈述：cardinalMk_le_lift_cardinalMk_of_commute (hc : forall s s' : S, Commute s 
s') : #(OreLocalization S X) <= lift.{u} #X
参数：hc : forall s s' : S, Commute s s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_surjective`：lift_mk_le_lift_mk_of_surject
ive {α : Type u} {β : Type v} {f : α -> β} (hf : Surjective f) : Cardinal.lift.{
u} (#β) <= Cardinal.lift.{v} (#…
· 使用定理 `OreLocalization.oreDiv_one_surjective_of_finite_right`：oreDiv_one_surjec
tive_of_finite_right [Finite X] : Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreL
ocalization S X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
-/
theorem cardinalMk_le_lift_cardinalMk_of_commute (hc : ∀ s s' : S, Commute s s') :
    #(OreLocalization S X) ≤ lift.{u} #X := by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rwa [lift_umax.{v, u}, lift_id'] at this
  have key (x : X) (s s' : S) (h : s • x = s' • x) (hc : Commute s s') : x /ₒ s = x /ₒ s' := by
    rw [oreDiv_eq_iff]
    refine ⟨s, s'.1, h, ?_⟩
    · exact_mod_cast hc
  let i (x : X × S) := x.1 /ₒ x.2
  have hsurj : Surjective i := Quotient.mk''_surjective
  have hi := rightInverse_surjInv hsurj
  let j := (fun x : X × S ↦ (x.1, x.2 • x.1)) ∘ surjInv hsurj
  suffices Injective j by
    have := lift_mk_le_lift_mk_of_injective this
    rwa [lift_umax.{v, u}, lift_id', mk_prod, lift_id, lift_mul, mul_eq_self (by simp)] at this
  intro
  grind

end OreLocalization

