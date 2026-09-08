/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-! # Basic Properties of Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main results

- `IsSimpleRing.instNontrivial`: simple rings are non-trivial.
- `DivisionRing.isSimpleRing`: division rings are simple.
- `RingHom.injective`: every ring homomorphism from a simple ring to a nontrivial ring is injective.
- `IsSimpleRing.iff_injective_ringHom`: a ring is simple iff every ring homomorphism to a nontrivial
  ring is injective.

-/

public section

variable (R : Type*) [NonUnitalNonAssocRing R]

namespace IsSimpleRing

variable {R}

/-
**IsSimpleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSimpleRing R] : Nontrivial R := by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  use x, 0, hx

attribute [instance 200] IsSimpleRing.instNontrivial
/-
**IsSimpleRing.one_mem_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSi
dedIdeal A) (hI : I != ⊥) : (1 : A) in I
参数：I : TwoSidedIdeal A；hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleRing.simple`：∀ {R : Type u_1} {inst : NonUnitalNonAssocRing R} [
self : IsSimpleRing R], IsSimpleOrder (TwoSidedIdeal R)
-/
lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I ≠ ⊥) : (1 : A) ∈ I :=
  (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩
/-
**IsSimpleRing.one_mem_of_ne_zero_mem** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : 
TwoSidedIdeal A) {x : A} (hx : x != 0) (hxI : x in I) : (1 : A) in I
参数：I : TwoSidedIdeal A；hx : x != 0；hxI : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSimpleRing.one_mem_of_ne_bot`：one_mem_of_ne_bot {A : Type*} [NonAssocR
ing A] [IsSimpleRing A] (I : TwoSidedIdeal A) (hI : I != ⊥) : (1 : A) in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    {x : A} (hx : x ≠ 0) (hxI : x ∈ I) : (1 : A) ∈ I :=
  one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)
/-
**IsSimpleRing.of_eq_bot_or_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：of_eq_bot_or_eq_top [Nontrivial R] (h : forall I : TwoSidedIdeal R, I = ⊥ 
∨ I = ⊤) : IsSimpleRing R where simple.eq_bot_or_eq_top
参数：h : forall I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoSidedIdeal.instNontrivial`：∀ {R : Type u_1} [inst : NonUnitalNonAssoc
Ring R] [Nontrivial R], Nontrivial (TwoSidedIdeal R)
-/
lemma of_eq_bot_or_eq_top [Nontrivial R] (h : ∀ I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤) :
    IsSimpleRing R where
  simple.eq_bot_or_eq_top := h
/-
**IsSimpleRing._root_.DivisionRing.isSimpleRing** 是 Mathlib 中的一个实例，位于命名空间 `IsSim
pleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.DivisionRing.isSimpleRing (A : Type*) [DivisionRing A] : IsSimpleRing A :=
  .of_eq_bot_or_eq_top <| fun I ↦ by
    rw [or_iff_not_imp_left, ← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x ≠ 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1
/-
**IsSimpleRing.injective_ringHom_or_subsingleton_codomain** 是 Mathlib 中的一个引理，位于命
名空间 `IsSimpleRing`。
形式化陈述：injective_ringHom_or_subsingleton_codomain {R S : Type*} [NonAssocRing R] 
[IsSimpleRing R] [NonAssocSemiring S] (f : R ->+* S) : Function.Injective f ∨ Su
bsingleton S
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `TwoSidedIdeal.ker_eq_bot`：ker_eq_bot : ker f = ⊥ ↔ Function.Injective f
· 使用定理 `subsingleton_iff_zero_eq_one`：subsingleton_iff_zero_eq_one : (0 : M₀) = 
1 ↔ Subsingleton M₀
· 使用引理 `TwoSidedIdeal.mem_top`：mem_top {x : R} : x in (⊤ : TwoSidedIdeal R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `TwoSidedIdeal.mem_ker`：mem_ker {x : R} : x in ker f ↔ f x = 0
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleRing.simple`：∀ {R : Type u_1} {inst : NonUnitalNonAssocRing R} [
self : IsSimpleRing R], IsSimpleOrder (TwoSidedIdeal R)
-/
lemma injective_ringHom_or_subsingleton_codomain
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S]
    (f : R →+* S) : Function.Injective f ∨ Subsingleton S :=
  simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f) |>.imp (TwoSidedIdeal.ker_eq_bot _ |>.1)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 ∈ TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)
/-
**IsSimpleRing._root_.RingHom.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleRing`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.RingHom.injective
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f :=
  injective_ringHom_or_subsingleton_codomain f |>.resolve_right fun r => not_subsingleton _ r

universe u in
/-
**IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain** 是 Mathlib 中的一个引理
，位于命名空间 `IsSimpleRing`。
形式化陈述：iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing 
R] [Nontrivial R] : IsSimpleRing R ↔ forall {S : Type u} [NonAssocSemiring S] (f
 : R ->+* S), Function.Injective f ∨ Subsingleton S where mp _ _ _
参数：R : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSimpleRing.injective_ringHom_or_subsingleton_codomain`：injective_ringH
om_or_subsingleton_codomain {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [Non
AssocSemiring S] (f : R ->+* S) : Function.In…
· 使用引理 `IsSimpleRing.of_eq_bot_or_eq_top`：of_eq_bot_or_eq_top [Nontrivial R] (h 
: forall I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤) : IsSimpleRing R where simple.eq_bo
t_or_eq_top
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TwoSidedIdeal.ker_ringCon_mk'`：ker_ringCon_mk' (I : TwoSidedIdeal R) : k
er I.ringCon.mk' = I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `TwoSidedIdeal.ker_eq_bot`：ker_eq_bot : ker f = ⊥ ↔ Function.Injective f
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] (f : R →+* S), Function.Injective f ∨ Subsingleton S where
  mp _ _ _ := injective_ringHom_or_subsingleton_codomain
  mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk' |>.imp
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.elim x 0)))

universe u in
/-
**IsSimpleRing.iff_injective_ringHom** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] : IsSim
pleRing R ↔ forall {S : Type u} [NonAssocSemiring S] [Nontrivial S] (f : R ->+* 
S), Function.Injective f
参数：R : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain`：iff_injecti
ve_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R]
 : IsSimpleRing R ↔ forall {S : Type u} [NonAssoc…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
-/
lemma iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] [Nontrivial S] (f : R →+* S), Function.Injective f :=
  iff_injective_ringHom_or_subsingleton_codomain R |>.trans <|
    ⟨fun H _ _ _ f => H f |>.resolve_right (by simpa [not_subsingleton_iff_nontrivial]),
      fun H S _ f => subsingleton_or_nontrivial S |>.recOn Or.inr fun _ => Or.inl <| H f⟩
/-
**IsSimpleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSimpleRing R] : IsSimpleRing Rᵐᵒᵖ := ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

end IsSimpleRing

