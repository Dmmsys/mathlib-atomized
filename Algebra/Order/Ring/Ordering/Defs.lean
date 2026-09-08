/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Ring orderings

Let `R` be a commutative ring. A preordering on `R` is a subset closed under
addition and multiplication that contains all squares, but not `-1`.

The support of a preordering `P` is the set of elements `x` such that both `x` and `-x` lie in `P`.

An ordering `O` on `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.

We define preorderings, supports and orderings.

A ring preordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

/-!
#### Preorderings
-/

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[ext]
/-
**RingPreordering** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：RingPreordering extends Subsemiring R where mem_of_isSquare' {x : R} (hx :
 IsSquare x) : x in carrier
参数：hx : IsSquare x。
继承自：Subsemiring R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`.
-/
structure RingPreordering extends Subsemiring R where
  mem_of_isSquare' {x : R} (hx : IsSquare x) : x ∈ carrier := by aesop
  neg_one_notMem' : -1 ∉ carrier := by aesop

namespace RingPreordering

attribute [coe] toSubsemiring

/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (RingPreordering R) := .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier → coe, as_prefix coe)
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

@[aesop unsafe 80% (rule_sets := [SetLike])]
/-
**RingPreordering.mem_of_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R) {x : R}, IsSq
uare x → x ∈ P
参数：P : RingPreordering R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.mem_of_isSquare'`：∀ {R : Type u_1} [inst : CommRing R] (
self : RingPreordering R) {x : R}, IsSquare x → x ∈ (↑self).carrier
-/
protected theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x ∈ P :=
  RingPreordering.mem_of_isSquare' _ hx

@[simp]
/-
**RingPreordering.mul_self_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R) (x : R), x * 
x ∈ P
参数：P : RingPreordering R；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.mem_of_isSquare`：∀ {R : Type u_1} [inst : CommRing R] (P
 : RingPreordering R) {x : R}, IsSquare x → x ∈ P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x ∈ P := by aesop

@[simp]
/-
**RingPreordering.pow_two_mem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R) (x : R), x ^ 
2 ∈ P
参数：P : RingPreordering R；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.mem_of_isSquare`：∀ {R : Type u_1} [inst : CommRing R] (P
 : RingPreordering R) {x : R}, IsSquare x → x ∈ P
· 使用引理 `IsSquare.sq`：IsSquare.sq (r : α) : IsSquare (r ^ 2)
-/
protected theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 ∈ P := by aesop

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
/-
**RingPreordering.neg_one_notMem** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R), -1 ∉ P
参数：P : RingPreordering R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.neg_one_notMem'`：∀ {R : Type u_1} [inst : CommRing R] (s
elf : RingPreordering R), -1 ∉ (↑self).carrier
-/
protected theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.neg_one_notMem' _
/-
**RingPreordering.toSubsemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingPreorde
ring`。
形式化陈述：toSubsemiring_injective : Function.Injective (toSubsemiring : RingPreorder
ing R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingPreordering.ext`：∀ {R : Type u_1} {inst : CommRing R} {x y : RingPre
ordering R}, (↑x).carrier = (↑y).carrier → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

@[simp]
/-
**RingPreordering.toSubsemiring_inj** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：toSubsemiring_inj {P₁ P₂ : RingPreordering R} : P₁.toSubsemiring = P₂.toSu
bsemiring ↔ P₁ = P₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RingPreordering.toSubsemiring_injective`：toSubsemiring_injective : Funct
ion.Injective (toSubsemiring : RingPreordering R -> _)
-/
theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

@[simp]
/-
**RingPreordering.mem_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：mem_toSubsemiring {P : RingPreordering R} {x : R} : x in P.toSubsemiring ↔
 x in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x ∈ P.toSubsemiring ↔ x ∈ P := .rfl

@[simp, norm_cast]
/-
**RingPreordering.coe_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P
参数：P : RingPreordering R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

@[simp]
/-
**RingPreordering.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x
 : R} : x in mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x in toSubsemirin
g
参数：mem_of_isSquare neg_one_notMem。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R} :
    x ∈ mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x ∈ toSubsemiring := .rfl

@[simp]
/-
**RingPreordering.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem
) : (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring
参数：toSubsemiring : Subsemiring R；mem_of_isSquare neg_one_notMem。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem) :
    (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring := rfl

section copy

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
/-
**RingPreordering.copy** 是 Mathlib 中的一个定义，位于命名空间 `RingPreordering`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → (P : RingPreordering R) → (S : Set 
R) → S = ↑P → RingPreordering R
参数：P : RingPreordering R；S : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a preordering with a new `carrier` equal to the old one. Useful to fix d
efinitional
equalities.
-/
protected def copy : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

attribute [norm_cast] coe_copy
/-
**RingPreordering.mem_copy** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (P : RingPreordering R) (S : Set R) (
hS : S = ↑P) {x : R}, x ∈ P.copy S hS ↔ x ∈ S
参数：P : RingPreordering R；S : Set R；hS : S = ↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_copy {x} : x ∈ P.copy S hS ↔ x ∈ S := .rfl
/-
**RingPreordering.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：copy_eq : P.copy S hS = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem copy_eq : P.copy S hS = S := rfl

end copy

variable {P : RingPreordering R}

/-!
#### Support
-/

section supportAddSubgroup

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
/-
**RingPreordering.supportAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `RingPreordering`
。
形式化陈述：supportAddSubgroup : AddSubgroup R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := P ∩ -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop
/-
**RingPreordering.mem_supportAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `RingPreorder
ing`。
形式化陈述：mem_supportAddSubgroup {x} : x in P.supportAddSubgroup ↔ x in P ∧ -x in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_supportAddSubgroup {x} : x ∈ P.supportAddSubgroup ↔ x ∈ P ∧ -x ∈ P := .rfl
/-
**RingPreordering.coe_supportAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `RingPreorder
ing`。
形式化陈述：coe_supportAddSubgroup : P.supportAddSubgroup = (P inter -P : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_supportAddSubgroup : P.supportAddSubgroup = (P ∩ -P : Set R) := rfl

end supportAddSubgroup

/-- Typeclass to track whether the support of a preordering forms an ideal. -/
/-
**RingPreordering.HasIdealSupport** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingPreordering`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → RingPreordering R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass to track whether the support of a preordering forms an ideal.
-/
class HasIdealSupport (P : RingPreordering R) : Prop where
  smul_mem_support (P) (x : R) {a : R} (ha : a ∈ P.supportAddSubgroup) :
    x * a ∈ P.supportAddSubgroup

export HasIdealSupport (smul_mem_support)
/-
**RingPreordering.hasIdealSupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering
`。
形式化陈述：hasIdealSupport_iff : P.HasIdealSupport ↔ forall x a : R, a in P -> -a in 
P -> x * a in P ∧ -(x * a) in P where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingPreordering.HasIdealSupport.smul_mem_support`：∀ {R : Type u_1} {inst
 : CommRing R} (P : RingPreordering R) [self : P.HasIdealSupport] (x : R) {a : R
},   a ∈ P.supportAddSubgroup → x * a …
-/
theorem hasIdealSupport_iff :
    P.HasIdealSupport ↔ ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P where
  mp _ := by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩
/-
**RingPreordering.** 是 Mathlib 中的一个实例，位于命名空间 `RingPreordering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasMemOrNegMem P] : P.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

variable [P.HasIdealSupport]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
/-
**RingPreordering.support** 是 Mathlib 中的一个定义，位于命名空间 `RingPreordering`。
形式化陈述：support : Ideal R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P
/-
**RingPreordering.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：mem_support {x} : x in P.support ↔ x in P ∧ -x in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support {x} : x ∈ P.support ↔ x ∈ P ∧ -x ∈ P := .rfl
/-
**RingPreordering.coe_support** 是 Mathlib 中的一个定理，位于命名空间 `RingPreordering`。
形式化陈述：coe_support : P.support = (P : Set R) inter -(P : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_support : P.support = (P : Set R) ∩ -(P : Set R) := rfl
/-
**RingPreordering.supportAddSubgroup_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingPreorderi
ng`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {P : RingPreordering R} [inst_1 : P.H
asIdealSupport],   P.supportAddSubgroup = Submodule.toAddSubgroup P.support
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem supportAddSubgroup_eq : P.supportAddSubgroup = P.support.toAddSubgroup := rfl

end support

/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
/-
**RingPreordering.IsOrdering** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingPreordering`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → RingPreordering R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering (P : RingPreordering R) extends HasMemOrNegMem P, P.support.IsPrime

end RingPreordering

