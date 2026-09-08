/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.RingTheory.Congruence.Opposite

/-!
# Two Sided Ideals

In this file, for any `Ring R`, we reinterpret `I : RingCon R` as a two-sided-ideal of a ring.

## Main definitions and results

* `TwoSidedIdeal`: For any `NonUnitalNonAssocRing R`, `TwoSidedIdeal R` is a wrapper around
  `RingCon R`.
* `TwoSidedIdeal.setLike`: Every `I : TwoSidedIdeal R` can be interpreted as a set of `R` where
  `x ∈ I` if and only if `I.ringCon x 0`.
* `TwoSidedIdeal.addCommGroup`: Every `I : TwoSidedIdeal R` is an abelian group.

-/

@[expose] public section

open MulOpposite

section definitions

/--
A two-sided ideal of a ring `R` is a subset of `R` that contains `0` and is closed under addition,
negation, and absorbs multiplication on both sides.
-/
/-
**TwoSidedIdeal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [NonUnitalNonAssocRing R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A two-sided ideal of a ring `R` is a subset of `R` that contains `0` and is clos
ed under addition,
negation, and absorbs multiplication on both sides.
-/
structure TwoSidedIdeal (R : Type*) [NonUnitalNonAssocRing R] where
  /-- In a ring, every two-sided ideal is induced by a ring congruence relation. -/
  ofRingCon ::
  /-- The congruence relation induced by this ideal. -/
  ringCon : RingCon R

end definitions

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (TwoSidedIdeal R) := by
  obtain ⟨I, J, h⟩ : Nontrivial (RingCon R) := inferInstance
  exact ⟨⟨I⟩, ⟨J⟩, by contrapose h; aesop⟩
/-
**TwoSidedIdeal.setLike** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
形式化陈述：setLike : SetLike (TwoSidedIdeal R) R where coe t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (TwoSidedIdeal R) R where
  coe t := {r | t.ringCon r 0}
  coe_injective := by
    rintro ⟨t₁⟩ ⟨t₂⟩ (h : {x | _} = {x | _})
    congr 1
    refine RingCon.ext fun a b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · have H' : a - b ∈ {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert! t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b ∈ {x | t₂ x 0} := sub_self b ▸ t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert! t₁.add H' (t₁.refl b) using 1 <;> abel
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (TwoSidedIdeal R) := .ofSetLike (TwoSidedIdeal R) R
/-
**TwoSidedIdeal.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_iff (x : R) : x in I ↔ I.ringCon x 0
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_iff (x : R) : x ∈ I ↔ I.ringCon x 0 := Iff.rfl

@[simp]
/-
**TwoSidedIdeal.mem_ofRingCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_ofRingCon {x : R} {c : RingCon R} : x in ofRingCon c ↔ c x 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofRingCon {x : R} {c : RingCon R} : x ∈ ofRingCon c ↔ c x 0 := Iff.rfl

@[simp, norm_cast]
/-
**TwoSidedIdeal.coe_ofRingCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_ofRingCon {c : RingCon R} : (ofRingCon c : Set R) = {x | c x 0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofRingCon {c : RingCon R} : (ofRingCon c : Set R) = {x | c x 0} := rfl

/-- A deprecated alias for `ofRingCon`. -/
@[deprecated ofRingCon (since := "2026-06-18")]
/-
**TwoSidedIdeal.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mk (c : RingCon R) : TwoSidedIdeal R
参数：c : RingCon R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A deprecated alias for `ofRingCon`.
-/
abbrev mk (c : RingCon R) : TwoSidedIdeal R := ofRingCon c

@[deprecated mem_ofRingCon (since := "2026-06-18")]
/-
**TwoSidedIdeal.mem_mk** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_mk {x : R} {c : RingCon R} : x in mk c ↔ c x 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mk {x : R} {c : RingCon R} : x ∈ mk c ↔ c x 0 := Iff.rfl

@[deprecated coe_ofRingCon (since := "2026-06-18")]
/-
**TwoSidedIdeal.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_mk {c : RingCon R} : (mk c : Set R) = {x | c x 0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk {c : RingCon R} : (mk c : Set R) = {x | c x 0} := rfl
/-
**TwoSidedIdeal.rel_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：rel_iff (x y : R) : I.ringCon x y ↔ x - y in I
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.RingTheory.TwoSidedIdeal.Basic.0.TwoSidedIdeal.rel_iff.
_abel_1_1`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (y : R), 0 = y - y
· 使用定理 `RingCon.sub`：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t : 
RingCon S) {a b c d : S}, t a b → t c d → t (a - c) (b - d)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
· 使用定理 `_private.Mathlib.RingTheory.TwoSidedIdeal.Basic.0.TwoSidedIdeal.setLike.
_abel_1`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (a b : R), a = a - b 
+ b
· 使用定理 `_private.Mathlib.RingTheory.TwoSidedIdeal.Basic.0.TwoSidedIdeal.setLike.
_abel_2`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (b : R), b = 0 + b
· 使用定理 `RingCon.add`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w + y) (x + z)
-/
lemma rel_iff (x y : R) : I.ringCon x y ↔ x - y ∈ I := by
  rw [mem_iff]
  constructor
  · intro h; convert! I.ringCon.sub h (I.ringCon.refl y); abel
  · intro h; convert! I.ringCon.add h (I.ringCon.refl y) <;> abel

/--
the coercion from two-sided-ideals to sets is an order embedding
-/
@[simps]
/-
**TwoSidedIdeal.coeOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coeOrderEmbedding : TwoSidedIdeal R ↪o Set R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the coercion from two-sided-ideals to sets is an order embedding
-/
def coeOrderEmbedding : TwoSidedIdeal R ↪o Set R where
  toFun := SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun (h : (I : Set R) ⊆ (J : Set R)) _ h' ↦ h h', fun h _ h' ↦ h h'⟩
/-
**TwoSidedIdeal.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：le_iff {I J : TwoSidedIdeal R} : I <= J ↔ (I : Set R) subseteq (J : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff {I J : TwoSidedIdeal R} : I ≤ J ↔ (I : Set R) ⊆ (J : Set R) := Iff.rfl

/-- Two-sided-ideals corresponds to congruence relations on a ring. -/
@[simps apply symm_apply]
/-
**TwoSidedIdeal.orderIsoRingCon** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：orderIsoRingCon : TwoSidedIdeal R ≃o RingCon R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two-sided-ideals corresponds to congruence relations on a ring.
-/
def orderIsoRingCon : TwoSidedIdeal R ≃o RingCon R where
  toFun := TwoSidedIdeal.ringCon
  invFun := ofRingCon
  map_rel_iff' {I J} := Iff.symm <| le_iff.trans ⟨fun h x y r => by rw [rel_iff] at r ⊢; exact h r,
    fun h x hx => by rw [SetLike.mem_coe, mem_iff] at hx ⊢; exact h hx⟩
/-
**TwoSidedIdeal.ringCon_injective** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ringCon_injective : Function.Injective (TwoSidedIdeal.ringCon (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringCon_injective : Function.Injective (TwoSidedIdeal.ringCon (R := R)) := by
  rintro ⟨x⟩ ⟨y⟩ rfl; rfl
/-
**TwoSidedIdeal.ringCon_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ringCon_le_iff {I J : TwoSidedIdeal R} : I <= J ↔ I.ringCon <= J.ringCon
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
lemma ringCon_le_iff {I J : TwoSidedIdeal R} : I ≤ J ↔ I.ringCon ≤ J.ringCon :=
  orderIsoRingCon.map_rel_iff.symm

@[ext]
/-
**TwoSidedIdeal.ext** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ext {I J : TwoSidedIdeal R} (h : forall x, x in I ↔ x in J) : I = J
参数：h : forall x, x in I ↔ x in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
lemma ext {I J : TwoSidedIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  coeOrderEmbedding.injective (Set.ext h)
/-
**TwoSidedIdeal.lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：lt_iff (I J : TwoSidedIdeal R) : I < J ↔ (I : Set R) ⊂ (J : Set R)
参数：I J : TwoSidedIdeal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Set.ssubset_iff_subset_ne`：∀ {α : Type u} {s t : Set α}, s ⊂ t ↔ s ⊆ t ∧
 s ≠ t
· 使用引理 `TwoSidedIdeal.le_iff`：le_iff {I J : TwoSidedIdeal R} : I <= J ↔ (I : Set
 R) subseteq (J : Set R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_iff (I J : TwoSidedIdeal R) : I < J ↔ (I : Set R) ⊂ (J : Set R) := by
  rw [lt_iff_le_and_ne, Set.ssubset_iff_subset_ne, le_iff]
  simp
/-
**TwoSidedIdeal.zero_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：zero_mem : 0 in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
-/
lemma zero_mem : 0 ∈ I := I.ringCon.refl 0
/-
**TwoSidedIdeal.add_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：add_mem {x y} (hx : x in I) (hy : y in I) : x + y in I
参数：hx : x in I；hy : y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RingCon.add`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w + y) (x + z)
-/
lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by simpa using! I.ringCon.add hx hy
/-
**TwoSidedIdeal.neg_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：neg_mem {x} (hx : x in I) : -x in I
参数：hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `RingCon.neg`：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t : 
RingCon S) {a b : S}, t a b → t (-a) (-b)
-/
lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by simpa using! I.ringCon.neg hx
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubgroupClass (TwoSidedIdeal R) R where
  zero_mem := zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _
/-
**TwoSidedIdeal.sub_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：sub_mem {x y} (hx : x in I) (hy : y in I) : x - y in I
参数：hx : x in I；hy : y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `TwoSidedIdeal.instAddSubgroupClass`：∀ {R : Type u_1} [inst : NonUnitalNo
nAssocRing R], AddSubgroupClass (TwoSidedIdeal R) R
-/
lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := _root_.sub_mem hx hy
/-
**TwoSidedIdeal.mul_mem_left** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mul_mem_left (x y) (hy : y in I) : x * y in I
参数：x y；hy : y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
-/
lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by
  simpa using! I.ringCon.mul (I.ringCon.refl x) hy
/-
**TwoSidedIdeal.mul_mem_right** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mul_mem_right (x y) (hx : x in I) : x * y in I
参数：x y；hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
-/
lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by
  simpa using! I.ringCon.mul hx (I.ringCon.refl y)
/-
**TwoSidedIdeal.nsmul_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：nsmul_mem {x} (n : Nat) (hx : x in I) : n • x in I
参数：n : Nat；hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TwoSidedIdeal.instAddSubgroupClass`：∀ {R : Type u_1} [inst : NonUnitalNo
nAssocRing R], AddSubgroupClass (TwoSidedIdeal R) R
-/
lemma nsmul_mem {x} (n : ℕ) (hx : x ∈ I) : n • x ∈ I := _root_.nsmul_mem hx _
/-
**TwoSidedIdeal.zsmul_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：zsmul_mem {x} (n : Int) (hx : x in I) : n • x in I
参数：n : Int；hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `TwoSidedIdeal.instAddSubgroupClass`：∀ {R : Type u_1} [inst : NonUnitalNo
nAssocRing R], AddSubgroupClass (TwoSidedIdeal R) R
-/
lemma zsmul_mem {x} (n : ℤ) (hx : x ∈ I) : n • x ∈ I := _root_.zsmul_mem hx _

/--
The "set-theoretic-way" of constructing a two-sided ideal by providing:
- the underlying set `S`;
- a proof that `0 ∈ S`;
- a proof that `x + y ∈ S` if `x ∈ S` and `y ∈ S`;
- a proof that `-x ∈ S` if `x ∈ S`;
- a proof that `x * y ∈ S` if `y ∈ S`;
- a proof that `x * y ∈ S` if `x ∈ S`.
-/
/-
**TwoSidedIdeal.mk'** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mk' (carrier : Set R) (zero_mem : 0 in carrier) (add_mem : forall {x y}, x
 in carrier -> y in carrier -> x + y in carrier) (neg_mem : forall {x}, x in car
rier -> -x in carrier) (mul_mem_left : forall {x y}, y in carrier -> x * y in ca
rrier) (mul_mem_right : forall {x y}, x in carrier -> x * y in carrier) : TwoSid
edIdeal R where ringCon
参数：carrier : Set R；zero_mem : 0 in carrier；add_mem : forall {x y}, x in carrier 
-> y in carrier -> x + y in carrier；neg_mem : forall {x}, x in carrier -> -x in 
carrier；mul_mem_left : forall {x y}, y in carrier -> x * y in carrier；mul_mem_ri
ght : forall {x y}, x in carrier -> x * y in carrier。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "set-theoretic-way" of constructing a two-sided ideal by providing:
- the underlying set `S`;
- a proof that `0 ∈ S`;
- a proof that `x + y ∈ S` if `x ∈ S` and `y ∈ S`;
- a proof that `-x ∈ S` if `x ∈ S`;
- a proof that `x * y ∈ S` if `y ∈ S`;
- a proof that `x * y ∈ S` if `x ∈ S`.
-/
def mk' (carrier : Set R)
    (zero_mem : 0 ∈ carrier)
    (add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
    (neg_mem : ∀ {x}, x ∈ carrier → -x ∈ carrier)
    (mul_mem_left : ∀ {x y}, y ∈ carrier → x * y ∈ carrier)
    (mul_mem_right : ∀ {x y}, x ∈ carrier → x * y ∈ carrier) : TwoSidedIdeal R where
  ringCon :=
    { r := fun x y ↦ x - y ∈ carrier
      iseqv :=
      { refl := fun x ↦ by simpa using zero_mem
        symm := fun h ↦ by simpa using neg_mem h
        trans := fun {x y z} h1 h2 ↦ by
          simpa only [show x - z = (x - y) + (y - z) by abel] using add_mem h1 h2 }
      mul' := fun {a b c d} (h1 : a - b ∈ carrier) (h2 : c - d ∈ carrier) ↦ show _ ∈ carrier by
        rw [show a * c - b * d = a * (c - d) + (a - b) * d by rw [mul_sub, sub_mul]; abel]
        exact add_mem (mul_mem_left h2) (mul_mem_right h1)
      add' := fun {a b c d} (h1 : a - b ∈ carrier) (h2 : c - d ∈ carrier) ↦ show _ ∈ carrier by
        rw [show a + c - (b + d) = (a - b) + (c - d) by abel]
        exact add_mem h1 h2 }

@[simp]
/-
**TwoSidedIdeal.mem_mk'** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_r
ight) (x : R) : x in mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_r
ight ↔ x in carrier
参数：carrier : Set R；zero_mem add_mem neg_mem mul_mem_left mul_mem_right；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) (x : R) :
    x ∈ mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right ↔ x ∈ carrier := by
  rw [mem_iff]
  simp [mk']

set_option linter.docPrime false in
@[simp]
/-
**TwoSidedIdeal.coe_mk'** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_r
ight) : (mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right : Set R
) = carrier
参数：carrier : Set R；zero_mem add_mem neg_mem mul_mem_left mul_mem_right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `TwoSidedIdeal.mem_mk'`：mem_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) (x : R) : x in mk' carrier zero_mem add_mem neg_m
em mul_mem_…
-/
lemma coe_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) :
    (mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right : Set R) = carrier :=
  Set.ext <| mem_mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (TwoSidedIdeal R) R R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_left _ _ _ h

-- This is not an instance, because together with the instance above,
-- it violates the `outParam` of `SMulMemClass`.
-- See: https://github.com/leanprover-community/mathlib4/pull/40718
/-
**TwoSidedIdeal.instSMulMemClassMulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedI
deal`。
形式化陈述：instSMulMemClassMulOpposite : SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R where 
smul_mem _ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.mul_mem_right`：mul_mem_right (x y) (hx : x in I) : x * y i
n I
-/
theorem instSMulMemClassMulOpposite : SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_right _ _ _ h
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero I where zero := ⟨0, I.zero_mem⟩
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ I where smul n x := ⟨n • x.1, I.nsmul_mem n x.2⟩
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ I where smul n x := ⟨n • x.1, I.zsmul_mem n x.2⟩
/-
**TwoSidedIdeal.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
形式化陈述：addCommGroup : AddCommGroup I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup I :=
  Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The coercion into the ring as a `AddMonoidHom` -/
@[simps]
/-
**TwoSidedIdeal.coeAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coeAddMonoidHom : I ->+ R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion into the ring as a `AddMonoidHom`
-/
def coeAddMonoidHom : I →+ R where
  toFun := (↑)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- If `I` is a two-sided ideal of `R`, then `{op x | x ∈ I}` is a two-sided ideal in `Rᵐᵒᵖ`. -/
@[simps]
/-
**TwoSidedIdeal.op** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：op (I : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ where ringCon
参数：I : TwoSidedIdeal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is a two-sided ideal of `R`, then `{op x | x ∈ I}` is a two-sided ideal i
n `Rᵐᵒᵖ`.
-/
def op (I : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ where
  ringCon := I.ringCon.op

@[simp]
/-
**TwoSidedIdeal.mem_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_op_iff {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} : x in I.op ↔ x.unop in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
-/
lemma mem_op_iff {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} : x ∈ I.op ↔ x.unop ∈ I :=
  I.ringCon.comm'

@[simp, norm_cast]
/-
**TwoSidedIdeal.coe_op** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_op {I : TwoSidedIdeal R} : (I.op : Set Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `TwoSidedIdeal.mem_op_iff`：mem_op_iff {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} : 
x in I.op ↔ x.unop in I
-/
lemma coe_op {I : TwoSidedIdeal R} : (I.op : Set Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I :=
  Set.ext fun _ => mem_op_iff


/-- If `I` is a two-sided ideal of `Rᵐᵒᵖ`, then `{x.unop | x ∈ I}` is a two-sided ideal in `R`. -/
@[simps]
/-
**TwoSidedIdeal.unop** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：unop (I : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R where ringCon
参数：I : TwoSidedIdeal Rᵐᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is a two-sided ideal of `Rᵐᵒᵖ`, then `{x.unop | x ∈ I}` is a two-sided id
eal in `R`.
-/
def unop (I : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R where
  ringCon := I.ringCon.unop

@[simp]
/-
**TwoSidedIdeal.mem_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_unop_iff {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R} : x in I.unop ↔ MulOpposite.
op x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
-/
lemma mem_unop_iff {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R} : x ∈ I.unop ↔ MulOpposite.op x ∈ I :=
  I.ringCon.comm'

@[simp, norm_cast]
/-
**TwoSidedIdeal.coe_unop** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_unop {I : TwoSidedIdeal Rᵐᵒᵖ} : (I.unop : Set R) = MulOpposite.op ⁻¹' 
I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `TwoSidedIdeal.mem_unop_iff`：mem_unop_iff {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R
} : x in I.unop ↔ MulOpposite.op x in I
-/
lemma coe_unop {I : TwoSidedIdeal Rᵐᵒᵖ} : (I.unop : Set R) = MulOpposite.op ⁻¹' I :=
  Set.ext fun _ => mem_unop_iff

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
/-
**TwoSidedIdeal.opOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：opOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
def opOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {I' J'} := by simpa [ringCon_le_iff] using RingCon.opOrderIso.map_rel_iff

end NonUnitalNonAssocRing

end TwoSidedIdeal

