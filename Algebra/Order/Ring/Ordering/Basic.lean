/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Ring orderings

We prove basic properties of (pre)orderings on rings and their supports.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {P : RingPreordering R}

/-!
### Preorderings
-/

namespace RingPreordering

@[gcongr]
/--
theorem `toSubsemiring_le_toSubsemiring` / 定理 `toSubsemiring_le_toSubsemiring`

English:
theorem toSubsemiring_le_toSubsemiring
  given: {P₁ P₂ : RingPreordering R}
  proof: .rfl

@[gcongr]

中文:
定理 toSubsemiring_le_toSubsemiring
  条件: {P₁ P₂ : RingPreordering R}
  证明: .rfl

@[gcongr]
-/
theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring <= P₂.toSubsemiring ↔ P₁ <= P₂ := .rfl

@[gcongr]
/--
theorem `toSubsemiring_lt_toSubsemiring` / 定理 `toSubsemiring_lt_toSubsemiring`

English:
theorem toSubsemiring_lt_toSubsemiring
  given: {P₁ P₂ : RingPreordering R}
  proof: .rfl

@[mono]

中文:
定理 toSubsemiring_lt_toSubsemiring
  条件: {P₁ P₂ : RingPreordering R}
  证明: .rfl

@[mono]
-/
theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

@[mono]
/--
theorem `toSubsemiring_mono` / 定理 `toSubsemiring_mono`

English:
theorem toSubsemiring_mono
  statement: Monotone (toSubsemiring : RingPreordering R -> _)
  proof: fun _ _ => id

@[mono]

中文:
定理 toSubsemiring_mono
  结论: 递增 (toSubsemiring : RingPreordering R -> _)
  证明: fun _ _ => id

@[mono]
-/
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R -> _) :=
  fun _ _ => id

@[mono]
/--
theorem `toSubsemiring_strictMono` / 定理 `toSubsemiring_strictMono`

English:
theorem toSubsemiring_strictMono
  statement: StrictMono (toSubsemiring : RingPreordering R -> _)
  proof: fun _ _ => id

@[aesop unsafe 90% apply (rule_sets := [SetLike])]

中文:
定理 toSubsemiring_strictMono
  结论: 严格递增 (toSubsemiring : RingPreordering R -> _)
  证明: fun _ _ => id

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
-/
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R -> _) :=
  fun _ _ => id

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
/--
theorem `unitsInv_mem` / 定理 `unitsInv_mem`

English:
theorem unitsInv_mem
  given: {a : Rˣ} (ha : ↑a in P)
  statement: ↑a⁻¹ in P
  proof: by
  have : (a * (a⁻¹ * a⁻¹) : R) in P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]

中文:
定理 unitsInv_mem
  条件: {a : Rˣ} (ha : ↑a in P)
  结论: ↑a⁻¹ in P
  证明: by
  have : (a * (a⁻¹ * a⁻¹) : R) in P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]

Depends on / 依赖: config, enableSimp
-/
theorem unitsInv_mem {a : Rˣ} (ha : ↑a in P) : ↑a⁻¹ in P := by
  have : (a * (a⁻¹ * a⁻¹) : R) in P := by aesop (config := { enableSimp := false })
  simp_all

@[aesop unsafe 90% apply (rule_sets := [SetLike])]
/--
theorem `inv_mem` / 定理 `inv_mem`

English:
theorem inv_mem
  given: {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a in P)
  proof: by
  have mem : a * (a⁻¹ * a⁻¹) in P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]

中文:
定理 inv_mem
  条件: {F : 类型} [域 F] {P : RingPreordering F} {a : F} (ha : a in P)
  证明: by
  have mem : a * (a⁻¹ * a⁻¹) in P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
-/
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a in P) :
    a⁻¹ in P := by
  have mem : a * (a⁻¹ * a⁻¹) in P := by aesop
  field_simp at mem
  simp_all

@[aesop unsafe 80% apply (rule_sets := [SetLike])]
/--
theorem `mem_of_isSumSq` / 定理 `mem_of_isSumSq`

English:
theorem mem_of_isSumSq
  given: {x : R} (hx : IsSumSq x)
  statement: x in P
  proof: by
  induction hx using IsSumSq.rec' <;> aesop

中文:
定理 mem_of_isSumSq
  条件: {x : R} (hx : 是SumSq x)
  结论: x in P
  证明: by
  induction hx using IsSumSq.rec' <;> aesop

Depends on / 依赖: IsSumSq, IsSumSq.rec
-/
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x in P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {R : Type*} [CommRing R] (P : Set R)
  body: P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

中文:
定义 mk'
  签名: {R : 类型} [交换环 R] (P : 集合 R)
  定义体: P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1
-/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : forall {x y : R}, x in P -> y in P -> x + y in P)
    (mul : forall {x y : R}, x in P -> y in P -> x * y in P)
    (sq : forall x : R, x * x in P)
    (neg_one : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  given: {x : R}
  statement: x in mk' P add mul sq neg_one ↔ x in P
  proof: .rfl

中文:
定理 mem_mk'
  条件: {x : R}
  结论: x in mk' P add mul sq neg_one ↔ x in P
  证明: .rfl
-/
@[simp] theorem mem_mk' {x : R} : x in mk' P add mul sq neg_one ↔ x in P := .rfl
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  statement: mk' P add mul sq neg_one = P
  proof: rfl

中文:
定理 coe_mk'
  结论: mk' P add mul sq neg_one = P
  证明: rfl
-/
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

/-!
### Supports
-/

section ne_top

variable (P)

/--
theorem `one_notMem_supportAddSubgroup` / 定理 `one_notMem_supportAddSubgroup`

English:
theorem one_notMem_supportAddSubgroup
  statement: 1 ∉ P.supportAddSubgroup
  proof: fun h => RingPreordering.neg_one_notMem P h.2

中文:
定理 one_notMem_supportAddSubgroup
  结论: 1 ∉ P.supportAddSubgroup
  证明: fun h => RingPreordering.neg_one_notMem P h.2

Depends on / 依赖: RingPreordering, RingPreordering.neg_one_notMem, neg_one_notMem
-/
theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2

/--
theorem `one_notMem_support` / 定理 `one_notMem_support`

English:
theorem one_notMem_support
  given: [P.HasIdealSupport]
  statement: 1 ∉ P.support
  proof: by
  simpa using one_notMem_supportAddSubgroup P

中文:
定理 one_notMem_support
  条件: [P.有IdealSupport]
  结论: 1 ∉ P.support
  证明: by
  simpa using one_notMem_supportAddSubgroup P

Depends on / 依赖: one_notMem_supportAddSubgroup
-/
theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

/--
theorem `supportAddSubgroup_ne_top` / 定理 `supportAddSubgroup_ne_top`

English:
theorem supportAddSubgroup_ne_top
  statement: P.supportAddSubgroup != ⊤
  proof: fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 in P.supportAddSubgroup).2

中文:
定理 supportAddSubgroup_ne_top
  结论: P.supportAddSubgroup != ⊤
  证明: fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 in P.supportAddSubgroup).2

Depends on / 依赖: P.supportAddSubgroup, RingPreordering, RingPreordering.neg_one_notMem, neg_one_notMem, supportAddSubgroup
-/
theorem supportAddSubgroup_ne_top : P.supportAddSubgroup != ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 in P.supportAddSubgroup).2

/--
theorem `support_ne_top` / 定理 `support_ne_top`

English:
theorem support_ne_top
  given: [P.HasIdealSupport]
  statement: P.support != ⊤
  proof: by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

中文:
定理 support_ne_top
  条件: [P.有IdealSupport]
  结论: P.support != ⊤
  证明: by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

Depends on / 依赖: Submodule, Submodule.toAddSubgroup, apply_fun, supportAddSubgroup_ne_top, toAddSubgroup
-/
theorem support_ne_top [P.HasIdealSupport] : P.support != ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

/--
theorem `IsOrdering.mk'` / 定理 `IsOrdering.mk'`

English:
theorem IsOrdering.mk'
  statement: [HasMemOrNegMem P]
  proof: support_ne_top P
  mem_or_mem' := h

中文:
定理 是Ordering.mk'
  结论: [有MemOrNegMem P]
  证明: support_ne_top P
  mem_or_mem' := h

Depends on / 依赖: support_ne_top
-/
theorem IsOrdering.mk' [HasMemOrNegMem P]
    (h : forall {x y}, x * y in P.support -> x in P.support ∨ y in P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  statement: [P.HasIdealSupport]
  proof: by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

中文:
定理 smul_mem
  结论: [P.有IdealSupport]
  证明: by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

Depends on / 依赖: HasIdealSupport, P.HasIdealSupport, hasIdealSupport_iff
-/
theorem smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a in P) (h₂a : -a in P) : x * a in P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

/--
theorem `neg_smul_mem` / 定理 `neg_smul_mem`

English:
theorem neg_smul_mem
  statement: [P.HasIdealSupport]
  proof: by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

中文:
定理 neg_smul_mem
  结论: [P.有IdealSupport]
  证明: by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

Depends on / 依赖: HasIdealSupport, P.HasIdealSupport, hasIdealSupport_iff
-/
theorem neg_smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a in P) (h₂a : -a in P) : -(x * a) in P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

/--
theorem `hasIdealSupport_of_isUnit_two` / 定理 `hasIdealSupport_of_isUnit_two`

English:
theorem hasIdealSupport_of_isUnit_two
  given: (h : IsUnit (2 : R))
  statement: P.HasIdealSupport
  proof: by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

中文:
定理 hasIdealSupport_of_isUnit_two
  条件: (h : 是单位 (2 : R))
  结论: P.有IdealSupport
  证明: by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

Depends on / 依赖: exists_right_inv, h.exists_right_inv, hasIdealSupport_iff, linear_combination, ring_nf, sub_eq_add_neg
-/
theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Fact (IsUnit (2 : R))] : P.HasIdealSupport
  body: hasIdealSupport_of_isUnit_two h.out

中文:
实例 [h
  签名: : Fact (是单位 (2 : R))] : P.有IdealSupport
  定义体: hasIdealSupport_of_isUnit_two h.out

Depends on / 依赖: h.out, hasIdealSupport_of_isUnit_two
-/
instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

variable {P} in
@[aesop unsafe 70% apply]
/--
theorem `eq_zero_of_mem_of_neg_mem` / 定理 `eq_zero_of_mem_of_neg_mem`

English:
theorem eq_zero_of_mem_of_neg_mem
  given: {x} (h : x in P) (h2 : -x in P)
  statement: x = 0
  proof: by
  by_contra
  have mem : -x * x⁻¹ in P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

中文:
定理 eq_zero_of_mem_of_neg_mem
  条件: {x} (h : x in P) (h2 : -x in P)
  结论: x = 0
  证明: by
  by_contra
  have mem : -x * x⁻¹ in P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem
-/
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x in P) (h2 : -x in P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ in P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

/--
theorem `supportAddSubgroup_eq_bot` / 定理 `supportAddSubgroup_eq_bot`

English:
theorem supportAddSubgroup_eq_bot
  statement: P.supportAddSubgroup = ⊥
  proof: by
  ext; aesop (add simp mem_supportAddSubgroup)

中文:
定理 supportAddSubgroup_eq_bot
  结论: P.supportAddSubgroup = ⊥
  证明: by
  ext; aesop (add simp mem_supportAddSubgroup)

Depends on / 依赖: mem_supportAddSubgroup
-/
theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.HasIdealSupport
  body: by simp [supportAddSubgroup_eq_bot]

中文:
实例 :
  签名: P.有IdealSupport
  定义体: by simp [supportAddSubgroup_eq_bot]

Depends on / 依赖: supportAddSubgroup_eq_bot
-/
instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

/--
theorem `support_eq_bot` / 定理 `support_eq_bot`

English:
theorem support_eq_bot
  statement: P.support = ⊥
  proof: by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

中文:
定理 support_eq_bot
  结论: P.support = ⊥
  证明: by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P
-/
@[simp] theorem support_eq_bot : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.support.IsPrime
  body: by simpa using Ideal.isPrime_bot

中文:
实例 :
  签名: P.support.是素
  定义体: by simpa using Ideal.isPrime_bot

Depends on / 依赖: Ideal.isPrime_bot, isPrime_bot
-/
instance : P.support.IsPrime := by simpa using Ideal.isPrime_bot

end Field

/--
theorem `isOrdering_iff` / 定理 `isOrdering_iff`

English:
theorem isOrdering_iff
  proof: by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b in P := by simpa using mul_mem (by aesop : -a in P) (by aesop : -b in P)
    have : a in P.support ∨ b in P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x in P ∨ -x in P) <;> simp_all [mem_support]

中文:
定理 isOrdering_iff
  证明: by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b in P := by simpa using mul_mem (by aesop : -a in P) (by aesop : -b in P)
    have : a in P.support ∨ b in P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x in P ∨ -x in P) <;> simp_all [mem_support]

Depends on / 依赖: HasMemOrNegMem, Ideal.IsPrime.mem_or_mem, IsOrdering, IsOrdering.mk, IsPrime, P.support, mem_or_mem, mem_support, mul_mem, support
-/
theorem isOrdering_iff :
    P.IsOrdering ↔ forall a b : R, -(a * b) in P -> a in P ∨ b in P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b in P := by simpa using mul_mem (by aesop : -a in P) (by aesop : -b in P)
    have : a in P.support ∨ b in P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x in P ∨ -x in P) <;> simp_all [mem_support]
end RingPreordering
