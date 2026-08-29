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
Definition of `TwoSidedIdeal` / `TwoSidedIdeal` 的定义

English:
structure TwoSidedIdeal
  parameters: (R : Type*) [NonUnitalNonAssocRing R]
  axioms and operations (2):
    - ofRingCon : :
    - ringCon : RingCon R

中文:
结构 TwoSided理想
  参数: (R : 类型) [非幺非结合环 R]
  公理与运算 (2 个):
    - ofRingCon : :
    - ringCon : RingCon R
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (TwoSidedIdeal R)
  body: by
  obtain ⟨I, J, h⟩ : Nontrivial (RingCon R) := inferInstance
  exact ⟨⟨I⟩, ⟨J⟩, by contrapose h; aesop⟩

中文:
实例 [非平凡
  签名: R] : 非平凡 (TwoSided理想 R)
  定义体: by
  obtain ⟨I, J, h⟩ : Nontrivial (RingCon R) := inferInstance
  exact ⟨⟨I⟩, ⟨J⟩, by contrapose h; aesop⟩

Depends on / 依赖: Nontrivial, RingCon, contrapose
-/
instance [Nontrivial R] : Nontrivial (TwoSidedIdeal R) := by
  obtain ⟨I, J, h⟩ : Nontrivial (RingCon R) := inferInstance
  exact ⟨⟨I⟩, ⟨J⟩, by contrapose h; aesop⟩

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (TwoSidedIdeal R) R where
  body: {r | t.ringCon r 0}
  coe_injective := by
    rintro ⟨t₁⟩ ⟨t₂⟩ (h : {x | _} = {x | _})
    congr 1
    refine RingCon.ext fun a b => ⟨fun H => ?_, fun H => ?_⟩
    · have H' : a - b in {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert! t₂.add H' (t₂.refl b) using 1 <

中文:
实例 setLike
  签名: : 集合状 (TwoSided理想 R) R where
  定义体: {r | t.ringCon r 0}
  coe_injective := by
    rintro ⟨t₁⟩ ⟨t₂⟩ (h : {x | _} = {x | _})
    congr 1
    refine RingCon.ext fun a b => ⟨fun H => ?_, fun H => ?_⟩
    · have H' : a - b in {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert! t₂.add H' (t₂.refl b) using 1 <

Depends on / 依赖: ringCon, t.ringCon
-/
instance setLike : SetLike (TwoSidedIdeal R) R where
  coe t := {r | t.ringCon r 0}
  coe_injective := by
    rintro ⟨t₁⟩ ⟨t₂⟩ (h : {x | _} = {x | _})
    congr 1
    refine RingCon.ext fun a b => ⟨fun H => ?_, fun H => ?_⟩
    · have H' : a - b in {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert! t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b in {x | t₂ x 0} := sub_self b ▸ t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert! t₁.add H' (t₁.refl b) using 1 <;> abel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (TwoSidedIdeal R)
  body: .ofSetLike (TwoSidedIdeal R) R

中文:
实例 :
  签名: 偏序 (TwoSided理想 R)
  定义体: .ofSetLike (TwoSidedIdeal R) R

Depends on / 依赖: TwoSidedIdeal, ofSetLike
-/
instance : PartialOrder (TwoSidedIdeal R) := .ofSetLike (TwoSidedIdeal R) R

/--
lemma `mem_iff` / 引理 `mem_iff`

English:
lemma mem_iff
  given: (x : R)
  statement: x in I ↔ I.ringCon x 0
  proof: Iff.rfl

@[simp]

中文:
引理 mem_iff
  条件: (x : R)
  结论: x in I ↔ I.ringCon x 0
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_iff (x : R) : x in I ↔ I.ringCon x 0 := Iff.rfl

@[simp]
/--
lemma `mem_ofRingCon` / 引理 `mem_ofRingCon`

English:
lemma mem_ofRingCon
  given: {x : R} {c : RingCon R}
  statement: x in ofRingCon c ↔ c x 0
  proof: Iff.rfl

@[simp, norm_cast]

中文:
引理 mem_ofRingCon
  条件: {x : R} {c : RingCon R}
  结论: x in ofRingCon c ↔ c x 0
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
lemma mem_ofRingCon {x : R} {c : RingCon R} : x in ofRingCon c ↔ c x 0 := Iff.rfl

@[simp, norm_cast]
/--
lemma `coe_ofRingCon` / 引理 `coe_ofRingCon`

English:
lemma coe_ofRingCon
  given: {c : RingCon R}
  statement: (ofRingCon c : Set R) = {x | c x 0}
  proof: rfl

中文:
引理 coe_ofRingCon
  条件: {c : RingCon R}
  结论: (ofRingCon c : 集合 R) = {x | c x 0}
  证明: rfl
-/
lemma coe_ofRingCon {c : RingCon R} : (ofRingCon c : Set R) = {x | c x 0} := rfl

/-- A deprecated alias for `ofRingCon`. -/
@[deprecated ofRingCon (since := "2026-06-18")]
/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (c : RingCon R)
  body: ofRingCon c

@[deprecated mem_ofRingCon (since := "2026-06-18")]

中文:
缩写 mk
  签名: (c : RingCon R)
  定义体: ofRingCon c

@[deprecated mem_ofRingCon (since := "2026-06-18")]

Depends on / 依赖: ofRingCon
-/
abbrev mk (c : RingCon R) : TwoSidedIdeal R := ofRingCon c

@[deprecated mem_ofRingCon (since := "2026-06-18")]
/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {x : R} {c : RingCon R}
  statement: x in mk c ↔ c x 0
  proof: Iff.rfl

@[deprecated coe_ofRingCon (since := "2026-06-18")]

中文:
引理 mem_mk
  条件: {x : R} {c : RingCon R}
  结论: x in mk c ↔ c x 0
  证明: Iff.rfl

@[deprecated coe_ofRingCon (since := "2026-06-18")]

Depends on / 依赖: Iff.rfl
-/
lemma mem_mk {x : R} {c : RingCon R} : x in mk c ↔ c x 0 := Iff.rfl

@[deprecated coe_ofRingCon (since := "2026-06-18")]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: {c : RingCon R}
  statement: (mk c : Set R) = {x | c x 0}
  proof: rfl

中文:
引理 coe_mk
  条件: {c : RingCon R}
  结论: (mk c : 集合 R) = {x | c x 0}
  证明: rfl
-/
lemma coe_mk {c : RingCon R} : (mk c : Set R) = {x | c x 0} := rfl

/--
lemma `rel_iff` / 引理 `rel_iff`

English:
lemma rel_iff
  given: (x y : R)
  statement: I.ringCon x y ↔ x - y in I
  proof: by
  rw [mem_iff]
  constructor
  · intro h; convert! I.ringCon.sub h (I.ringCon.refl y); abel
  · intro h; convert! I.ringCon.add h (I.ringCon.refl y) <;> abel

中文:
引理 rel_iff
  条件: (x y : R)
  结论: I.ringCon x y ↔ x - y in I
  证明: by
  rw [mem_iff]
  constructor
  · intro h; convert! I.ringCon.sub h (I.ringCon.refl y); abel
  · intro h; convert! I.ringCon.add h (I.ringCon.refl y) <;> abel

Depends on / 依赖: I.ringCon.add, I.ringCon.refl, I.ringCon.sub, convert, mem_iff, ringCon
-/
lemma rel_iff (x y : R) : I.ringCon x y ↔ x - y in I := by
  rw [mem_iff]
  constructor
  · intro h; convert! I.ringCon.sub h (I.ringCon.refl y); abel
  · intro h; convert! I.ringCon.add h (I.ringCon.refl y) <;> abel

/--
the coercion from two-sided-ideals to sets is an order embedding
-/
@[simps]
/--
Definition of `coeOrderEmbedding` / `coeOrderEmbedding` 的定义

English:
definition coeOrderEmbedding
  signature: : TwoSidedIdeal R ↪o Set R where
  body: SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun (h : (I : Set R) subseteq (J : Set R)) _ h' => h h', fun h _ h' => h h'⟩

中文:
定义 coeOrderEmbedding
  签名: : TwoSided理想 R ↪o 集合 R where
  定义体: SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun (h : (I : Set R) subseteq (J : Set R)) _ h' => h h', fun h _ h' => h h'⟩

Depends on / 依赖: SetLike, SetLike.coe
-/
def coeOrderEmbedding : TwoSidedIdeal R ↪o Set R where
  toFun := SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun (h : (I : Set R) subseteq (J : Set R)) _ h' => h h', fun h _ h' => h h'⟩

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {I J : TwoSidedIdeal R}
  statement: I <= J ↔ (I : Set R) subseteq (J : Set R)
  proof: Iff.rfl

中文:
引理 le_iff
  条件: {I J : TwoSided理想 R}
  结论: I <= J ↔ (I : 集合 R) subseteq (J : 集合 R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_iff {I J : TwoSidedIdeal R} : I <= J ↔ (I : Set R) subseteq (J : Set R) := Iff.rfl

/-- Two-sided-ideals corresponds to congruence relations on a ring. -/
@[simps apply symm_apply]
/--
Definition of `orderIsoRingCon` / `orderIsoRingCon` 的定义

English:
definition orderIsoRingCon
  signature: : TwoSidedIdeal R ≃o RingCon R where
  body: TwoSidedIdeal.ringCon
  invFun := ofRingCon
map_rel_iff' {I J} := Iff.symm le_iff.trans ⟨fun h x y r => by rw [rel_iff] at r ⊢; exact h r,
    fun h x hx => by rw [SetLike.mem_coe, mem_iff] at hx ⊢; exact h hx⟩

中文:
定义 orderIsoRingCon
  签名: : TwoSided理想 R ≃o RingCon R where
  定义体: TwoSidedIdeal.ringCon
  invFun := ofRingCon
map_rel_iff' {I J} := Iff.symm le_iff.trans ⟨fun h x y r => by rw [rel_iff] at r ⊢; exact h r,
    fun h x hx => by rw [SetLike.mem_coe, mem_iff] at hx ⊢; exact h hx⟩

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.ringCon, ringCon
-/
def orderIsoRingCon : TwoSidedIdeal R ≃o RingCon R where
  toFun := TwoSidedIdeal.ringCon
  invFun := ofRingCon
map_rel_iff' {I J} := Iff.symm le_iff.trans ⟨fun h x y r => by rw [rel_iff] at r ⊢; exact h r,
    fun h x hx => by rw [SetLike.mem_coe, mem_iff] at hx ⊢; exact h hx⟩

/--
lemma `ringCon_injective` / 引理 `ringCon_injective`

English:
lemma ringCon_injective
  statement: Function.Injective (TwoSidedIdeal.ringCon (R := R))
  proof: by
  rintro ⟨x⟩ ⟨y⟩ rfl; rfl

中文:
引理 ringCon_injective
  结论: 函数.单射 (TwoSided理想.ringCon (R := R))
  证明: by
  rintro ⟨x⟩ ⟨y⟩ rfl; rfl
-/
lemma ringCon_injective : Function.Injective (TwoSidedIdeal.ringCon (R := R)) := by
  rintro ⟨x⟩ ⟨y⟩ rfl; rfl

/--
lemma `ringCon_le_iff` / 引理 `ringCon_le_iff`

English:
lemma ringCon_le_iff
  given: {I J : TwoSidedIdeal R}
  statement: I <= J ↔ I.ringCon <= J.ringCon
  proof: orderIsoRingCon.map_rel_iff.symm

@[ext]

中文:
引理 ringCon_le_iff
  条件: {I J : TwoSided理想 R}
  结论: I <= J ↔ I.ringCon <= J.ringCon
  证明: orderIsoRingCon.map_rel_iff.symm

@[ext]

Depends on / 依赖: map_rel_iff, orderIsoRingCon, orderIsoRingCon.map_rel_iff.symm
-/
lemma ringCon_le_iff {I J : TwoSidedIdeal R} : I <= J ↔ I.ringCon <= J.ringCon :=
  orderIsoRingCon.map_rel_iff.symm

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {I J : TwoSidedIdeal R} (h : forall x, x in I ↔ x in J)
  statement: I = J
  proof: coeOrderEmbedding.injective (Set.ext h)

中文:
引理 ext
  条件: {I J : TwoSided理想 R} (h : 对任意 x, x in I ↔ x in J)
  结论: I = J
  证明: coeOrderEmbedding.injective (Set.ext h)

Depends on / 依赖: RCLike, Set.ext, coeOrderEmbedding, coeOrderEmbedding.injective, injective, instContinuousSqrtRCLike
-/
lemma ext {I J : TwoSidedIdeal R} (h : forall x, x in I ↔ x in J) : I = J :=
  coeOrderEmbedding.injective (Set.ext h)

/--
lemma `lt_iff` / 引理 `lt_iff`

English:
lemma lt_iff
  given: (I J : TwoSidedIdeal R)
  statement: I < J ↔ (I : Set R) ⊂ (J : Set R)
  proof: by
  rw [lt_iff_le_and_ne]; rw [Set.ssubset_iff_subset_ne]; rw [le_iff]
  simp

中文:
引理 lt_iff
  条件: (I J : TwoSided理想 R)
  结论: I < J ↔ (I : 集合 R) ⊂ (J : 集合 R)
  证明: by
  rw [lt_iff_le_and_ne]; rw [Set.ssubset_iff_subset_ne]; rw [le_iff]
  simp

Depends on / 依赖: Set.ssubset_iff_subset_ne, le_iff, lt_iff_le_and_ne, ssubset_iff_subset_ne
-/
lemma lt_iff (I J : TwoSidedIdeal R) : I < J ↔ (I : Set R) ⊂ (J : Set R) := by
  rw [lt_iff_le_and_ne]; rw [Set.ssubset_iff_subset_ne]; rw [le_iff]
  simp

/--
lemma `zero_mem` / 引理 `zero_mem`

English:
lemma zero_mem
  statement: 0 in I
  proof: I.ringCon.refl 0

中文:
引理 zero_mem
  结论: 0 in I
  证明: I.ringCon.refl 0

Depends on / 依赖: I.ringCon.refl, ringCon
-/
lemma zero_mem : 0 in I := I.ringCon.refl 0

/--
lemma `add_mem` / 引理 `add_mem`

English:
lemma add_mem
  given: {x y} (hx : x in I) (hy : y in I)
  statement: x + y in I
  proof: by simpa using! I.ringCon.add hx hy

中文:
引理 add_mem
  条件: {x y} (hx : x in I) (hy : y in I)
  结论: x + y in I
  证明: by simpa using! I.ringCon.add hx hy

Depends on / 依赖: I.ringCon.add, ringCon
-/
lemma add_mem {x y} (hx : x in I) (hy : y in I) : x + y in I := by simpa using! I.ringCon.add hx hy

/--
lemma `neg_mem` / 引理 `neg_mem`

English:
lemma neg_mem
  given: {x} (hx : x in I)
  statement: -x in I
  proof: by simpa using! I.ringCon.neg hx

中文:
引理 neg_mem
  条件: {x} (hx : x in I)
  结论: -x in I
  证明: by simpa using! I.ringCon.neg hx

Depends on / 依赖: I.ringCon.neg, ringCon
-/
lemma neg_mem {x} (hx : x in I) : -x in I := by simpa using! I.ringCon.neg hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubgroupClass (TwoSidedIdeal R) R
  body: zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _

中文:
实例 :
  签名: 加法子群类 (TwoSided理想 R) R
  定义体: zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _

Depends on / 依赖: toContinuousMap, zero_mem
-/
instance : AddSubgroupClass (TwoSidedIdeal R) R where
  zero_mem := zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _

/--
lemma `sub_mem` / 引理 `sub_mem`

English:
lemma sub_mem
  given: {x y} (hx : x in I) (hy : y in I)
  statement: x - y in I
  proof: _root_.sub_mem hx hy

中文:
引理 sub_mem
  条件: {x y} (hx : x in I) (hy : y in I)
  结论: x - y in I
  证明: _root_.sub_mem hx hy

Depends on / 依赖: _root_, _root_.sub_mem, sub_mem
-/
lemma sub_mem {x y} (hx : x in I) (hy : y in I) : x - y in I := _root_.sub_mem hx hy

/--
lemma `mul_mem_left` / 引理 `mul_mem_left`

English:
lemma mul_mem_left
  given: (x y) (hy : y in I)
  statement: x * y in I
  proof: by
  simpa using! I.ringCon.mul (I.ringCon.refl x) hy

中文:
引理 mul_mem_left
  条件: (x y) (hy : y in I)
  结论: x * y in I
  证明: by
  simpa using! I.ringCon.mul (I.ringCon.refl x) hy

Depends on / 依赖: I.ringCon.mul, I.ringCon.refl, ringCon
-/
lemma mul_mem_left (x y) (hy : y in I) : x * y in I := by
  simpa using! I.ringCon.mul (I.ringCon.refl x) hy

/--
lemma `mul_mem_right` / 引理 `mul_mem_right`

English:
lemma mul_mem_right
  given: (x y) (hx : x in I)
  statement: x * y in I
  proof: by
  simpa using! I.ringCon.mul hx (I.ringCon.refl y)

中文:
引理 mul_mem_right
  条件: (x y) (hx : x in I)
  结论: x * y in I
  证明: by
  simpa using! I.ringCon.mul hx (I.ringCon.refl y)

Depends on / 依赖: I.ringCon.mul, I.ringCon.refl, ringCon
-/
lemma mul_mem_right (x y) (hx : x in I) : x * y in I := by
  simpa using! I.ringCon.mul hx (I.ringCon.refl y)

/--
lemma `nsmul_mem` / 引理 `nsmul_mem`

English:
lemma nsmul_mem
  given: {x} (n : Nat) (hx : x in I)
  statement: n • x in I
  proof: _root_.nsmul_mem hx _

中文:
引理 nsmul_mem
  条件: {x} (n : 自然数) (hx : x in I)
  结论: n • x in I
  证明: _root_.nsmul_mem hx _

Depends on / 依赖: _root_, _root_.nsmul_mem, nsmul_mem
-/
lemma nsmul_mem {x} (n : Nat) (hx : x in I) : n • x in I := _root_.nsmul_mem hx _

/--
lemma `zsmul_mem` / 引理 `zsmul_mem`

English:
lemma zsmul_mem
  given: {x} (n : Int) (hx : x in I)
  statement: n • x in I
  proof: _root_.zsmul_mem hx _

中文:
引理 zsmul_mem
  条件: {x} (n : 整数) (hx : x in I)
  结论: n • x in I
  证明: _root_.zsmul_mem hx _

Depends on / 依赖: _root_, _root_.zsmul_mem, zsmul_mem
-/
lemma zsmul_mem {x} (n : Int) (hx : x in I) : n • x in I := _root_.zsmul_mem hx _

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (carrier : Set R)
  body: { r := fun x y => x - y in carrier
      iseqv :=
      { refl := fun x => by simpa using zero_mem
        symm := fun h => by simpa using neg_mem h
        trans := fun {x y z} h1 h2 => by
          simpa only [show x - z = (x - y) + (y - z) by abel] using add_mem h1 h2 }
      mul' := fun {a b c d

中文:
定义 mk'
  签名: (carrier : 集合 R)
  定义体: { r := fun x y => x - y in carrier
      iseqv :=
      { refl := fun x => by simpa using zero_mem
        symm := fun h => by simpa using neg_mem h
        trans := fun {x y z} h1 h2 => by
          simpa only [show x - z = (x - y) + (y - z) by abel] using add_mem h1 h2 }
      mul' := fun {a b c d

Depends on / 依赖: add_mem, carrier, mul_mem_left, mul_mem_right, mul_sub, neg_mem, sub_mul, zero_mem
-/
def mk' (carrier : Set R)
    (zero_mem : 0 in carrier)
    (add_mem : forall {x y}, x in carrier -> y in carrier -> x + y in carrier)
    (neg_mem : forall {x}, x in carrier -> -x in carrier)
    (mul_mem_left : forall {x y}, y in carrier -> x * y in carrier)
    (mul_mem_right : forall {x y}, x in carrier -> x * y in carrier) : TwoSidedIdeal R where
  ringCon :=
    { r := fun x y => x - y in carrier
      iseqv :=
      { refl := fun x => by simpa using zero_mem
        symm := fun h => by simpa using neg_mem h
        trans := fun {x y z} h1 h2 => by
          simpa only [show x - z = (x - y) + (y - z) by abel] using add_mem h1 h2 }
      mul' := fun {a b c d} (h1 : a - b in carrier) (h2 : c - d in carrier) => show _ in carrier by
        rw [show a * c - b * d = a * (c - d) + (a - b) * d by rw [mul_sub]; rw [sub_mul]; abel]
        exact add_mem (mul_mem_left h2) (mul_mem_right h1)
      add' := fun {a b c d} (h1 : a - b in carrier) (h2 : c - d in carrier) => show _ in carrier by
        rw [show a + c - (b + d) = (a - b) + (c - d) by abel]
        exact add_mem h1 h2 }

@[simp]
/--
lemma `mem_mk'` / 引理 `mem_mk'`

English:
lemma mem_mk'
  given: (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) (x : R)
  proof: by
  rw [mem_iff]
  simp [mk']

中文:
引理 mem_mk'
  条件: (carrier : 集合 R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) (x : R)
  证明: by
  rw [mem_iff]
  simp [mk']

Depends on / 依赖: mem_iff
-/
lemma mem_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) (x : R) :
    x in mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right ↔ x in carrier := by
  rw [mem_iff]
  simp [mk']

set_option linter.docPrime false in
@[simp]
/--
lemma `coe_mk'` / 引理 `coe_mk'`

English:
lemma coe_mk'
  given: (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right)
  proof: Set.ext mem_mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right

中文:
引理 coe_mk'
  条件: (carrier : 集合 R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right)
  证明: Set.ext mem_mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right

Depends on / 依赖: Set.ext, add_mem, carrier, mem_mk, mul_mem_left, mul_mem_right, neg_mem, zero_mem
-/
lemma coe_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) :
    (mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right : Set R) = carrier :=
Set.ext mem_mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (TwoSidedIdeal R) R R
  body: TwoSidedIdeal.mul_mem_left _ _ _ h

中文:
实例 :
  签名: SMulMem类 (TwoSided理想 R) R R
  定义体: TwoSidedIdeal.mul_mem_left _ _ _ h

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.mul_mem_left, mul_mem_left
-/
instance : SMulMemClass (TwoSidedIdeal R) R R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_left _ _ _ h

-- This is not an instance, because together with the instance above,
-- it violates the `outParam` of `SMulMemClass`.
-- See: https://github.com/leanprover-community/mathlib4/pull/40718
/--
theorem `instSMulMemClassMulOpposite` / 定理 `instSMulMemClassMulOpposite`

English:
theorem instSMulMemClassMulOpposite
  statement: SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R where
  proof: TwoSidedIdeal.mul_mem_right _ _ _ h

中文:
定理 instSMulMemClassMulOpposite
  结论: SMulMem类 (TwoSided理想 R) Rᵐᵒᵖ R where
  证明: TwoSidedIdeal.mul_mem_right _ _ _ h

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.mul_mem_right, mul_mem_right
-/
theorem instSMulMemClassMulOpposite : SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_right _ _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add I
  body: ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

中文:
实例 :
  签名: 加法 I
  定义体: ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

Depends on / 依赖: I.add_mem, add_mem
-/
instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero I
  body: ⟨0, I.zero_mem⟩

中文:
实例 :
  签名: 零 I
  定义体: ⟨0, I.zero_mem⟩

Depends on / 依赖: I.zero_mem, zero_mem
-/
instance : Zero I where zero := ⟨0, I.zero_mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat I
  body: ⟨n • x.1, I.nsmul_mem n x.2⟩

中文:
实例 :
  签名: 标量乘法 自然数 I
  定义体: ⟨n • x.1, I.nsmul_mem n x.2⟩

Depends on / 依赖: I.nsmul_mem, nsmul_mem
-/
instance : SMul Nat I where smul n x := ⟨n • x.1, I.nsmul_mem n x.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg I
  body: ⟨-x.1, I.neg_mem x.2⟩

中文:
实例 :
  签名: 取负 I
  定义体: ⟨-x.1, I.neg_mem x.2⟩

Depends on / 依赖: I.neg_mem, neg_mem
-/
instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub I
  body: ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

中文:
实例 :
  签名: 减法 I
  定义体: ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

Depends on / 依赖: I.sub_mem, sub_mem
-/
instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int I
  body: ⟨n • x.1, I.zsmul_mem n x.2⟩

中文:
实例 :
  签名: 标量乘法 整数 I
  定义体: ⟨n • x.1, I.zsmul_mem n x.2⟩

Depends on / 依赖: I.zsmul_mem, zsmul_mem
-/
instance : SMul Int I where smul n x := ⟨n • x.1, I.zsmul_mem n x.2⟩

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup I
  body: Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 addCommGroup
  签名: : 加法交换群 I
  定义体: Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Function, Function.Injective.addCommGroup, Injective, Subtype, Subtype.coe_injective, addCommGroup, coe_injective
-/
instance addCommGroup : AddCommGroup I :=
  Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The coercion into the ring as a `AddMonoidHom` -/
@[simps]
/--
Definition of `coeAddMonoidHom` / `coeAddMonoidHom` 的定义

English:
definition coeAddMonoidHom
  signature: : I ->+ R where
  body: (↑)
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 coeAddMonoidHom
  签名: : I ->+ R where
  定义体: (↑)
  map_zero' := rfl
  map_add' _ _ := rfl
-/
def coeAddMonoidHom : I ->+ R where
  toFun := (↑)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- If `I` is a two-sided ideal of `R`, then `{op x | x ∈ I}` is a two-sided ideal in `Rᵐᵒᵖ`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (I : TwoSidedIdeal R)
  body: I.ringCon.op

@[simp]

中文:
定义 op
  签名: (I : TwoSided理想 R)
  定义体: I.ringCon.op

@[simp]

Depends on / 依赖: I.ringCon.op, ringCon
-/
def op (I : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ where
  ringCon := I.ringCon.op

@[simp]
/--
lemma `mem_op_iff` / 引理 `mem_op_iff`

English:
lemma mem_op_iff
  given: {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ}
  statement: x in I.op ↔ x.unop in I
  proof: I.ringCon.comm'

@[simp, norm_cast]

中文:
引理 mem_op_iff
  条件: {I : TwoSided理想 R} {x : Rᵐᵒᵖ}
  结论: x in I.op ↔ x.unop in I
  证明: I.ringCon.comm'

@[simp, norm_cast]

Depends on / 依赖: I.ringCon.comm, ringCon
-/
lemma mem_op_iff {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} : x in I.op ↔ x.unop in I :=
  I.ringCon.comm'

@[simp, norm_cast]
/--
lemma `coe_op` / 引理 `coe_op`

English:
lemma coe_op
  given: {I : TwoSidedIdeal R}
  statement: (I.op : Set Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I
  proof: Set.ext fun _ => mem_op_iff

中文:
引理 coe_op
  条件: {I : TwoSided理想 R}
  结论: (I.op : 集合 Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I
  证明: Set.ext fun _ => mem_op_iff

Depends on / 依赖: Set.ext, mem_op_iff
-/
lemma coe_op {I : TwoSidedIdeal R} : (I.op : Set Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I :=
  Set.ext fun _ => mem_op_iff


/-- If `I` is a two-sided ideal of `Rᵐᵒᵖ`, then `{x.unop | x ∈ I}` is a two-sided ideal in `R`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (I : TwoSidedIdeal Rᵐᵒᵖ)
  body: I.ringCon.unop

@[simp]

中文:
定义 unop
  签名: (I : TwoSided理想 Rᵐᵒᵖ)
  定义体: I.ringCon.unop

@[simp]

Depends on / 依赖: I.ringCon.unop, ringCon
-/
def unop (I : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R where
  ringCon := I.ringCon.unop

@[simp]
/--
lemma `mem_unop_iff` / 引理 `mem_unop_iff`

English:
lemma mem_unop_iff
  given: {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R}
  statement: x in I.unop ↔ MulOpposite.op x in I
  proof: I.ringCon.comm'

@[simp, norm_cast]

中文:
引理 mem_unop_iff
  条件: {I : TwoSided理想 Rᵐᵒᵖ} {x : R}
  结论: x in I.unop ↔ MulOpposite.op x in I
  证明: I.ringCon.comm'

@[simp, norm_cast]

Depends on / 依赖: I.ringCon.comm, ringCon
-/
lemma mem_unop_iff {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R} : x in I.unop ↔ MulOpposite.op x in I :=
  I.ringCon.comm'

@[simp, norm_cast]
/--
lemma `coe_unop` / 引理 `coe_unop`

English:
lemma coe_unop
  given: {I : TwoSidedIdeal Rᵐᵒᵖ}
  statement: (I.unop : Set R) = MulOpposite.op ⁻¹' I
  proof: Set.ext fun _ => mem_unop_iff

中文:
引理 coe_unop
  条件: {I : TwoSided理想 Rᵐᵒᵖ}
  结论: (I.unop : 集合 R) = MulOpposite.op ⁻¹' I
  证明: Set.ext fun _ => mem_unop_iff

Depends on / 依赖: Set.ext, mem_unop_iff
-/
lemma coe_unop {I : TwoSidedIdeal Rᵐᵒᵖ} : (I.unop : Set R) = MulOpposite.op ⁻¹' I :=
  Set.ext fun _ => mem_unop_iff

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
/--
Definition of `opOrderIso` / `opOrderIso` 的定义

English:
definition opOrderIso
  signature: : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  body: op
  invFun := unop
  map_rel_iff' {I' J'} := by simpa [ringCon_le_iff] using RingCon.opOrderIso.map_rel_iff

中文:
定义 opOrderIso
  签名: : TwoSided理想 R ≃o TwoSided理想 Rᵐᵒᵖ where
  定义体: op
  invFun := unop
  map_rel_iff' {I' J'} := by simpa [ringCon_le_iff] using RingCon.opOrderIso.map_rel_iff
-/
def opOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {I' J'} := by simpa [ringCon_le_iff] using RingCon.opOrderIso.map_rel_iff

end NonUnitalNonAssocRing

end TwoSidedIdeal
