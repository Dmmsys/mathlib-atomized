/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Tactic.FastInstance

/-!
# Bundled non-unital subsemirings

We define bundled non-unital subsemirings and some standard constructions:
`subtype` and `inclusion` ring homomorphisms.
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section neg_mul

variable {R S : Type*} [Mul R] [HasDistribNeg R] [SetLike S R] [MulMemClass S R] {s : S}

/-- This lemma exists for `aesop`, as `aesop` simplifies `-x * y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
/-
**neg_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul_mem {x y : R} (hx : -x in s) (hy : y in s) : -(x * y) in s
参数：hx : -x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…

--- 原说明 ---
This lemma exists for `aesop`, as `aesop` simplifies `-x * y` to `-(x * y)` befo
re applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does
 not hold.
-/
theorem neg_mul_mem {x y : R} (hx : -x ∈ s) (hy : y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy

/-- This lemma exists for `aesop`, as `aesop` simplifies `x * -y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
/-
**mul_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg_mem {x y : R} (hx : x in s) (hy : -y in s) : -(x * y) in s
参数：hx : x in s；hy : -y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…

--- 原说明 ---
This lemma exists for `aesop`, as `aesop` simplifies `x * -y` to `-(x * y)` befo
re applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does
 not hold.
-/
theorem mul_neg_mem {x y : R} (hx : x ∈ s) (hy : -y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy

-- doesn't work without the above `aesop` lemmas
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {x y z : R} (hx : x ∈ s) (hy : -y ∈ s) (hz : z ∈ s) :
    x * (-y) * z ∈ s := by aesop

end neg_mul

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R]

/-- `NonUnitalSubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both an additive submonoid and also a multiplicative subsemigroup. -/
/-
**NonUnitalSubsemiringClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u)) → [NonUnitalNonAssocSemiring R] →
 [SetLike S R] → Prop
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalSubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` tha
t
are both an additive submonoid and also a multiplicative subsemigroup.
-/
class NonUnitalSubsemiringClass (S : Type*) (R : outParam (Type u)) [NonUnitalNonAssocSemiring R]
    [SetLike S R] : Prop
  extends AddSubmonoidClass S R where
  mul_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a * b ∈ s

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalSubsemiringClass.mulMemClass (S : Type*) (R : Type u)
    [NonUnitalNonAssocSemiring R] [SetLike S R] [h : NonUnitalSubsemiringClass S R] :
    MulMemClass S R :=
  { h with }

namespace NonUnitalSubsemiringClass

variable [SetLike S R] [NonUnitalSubsemiringClass S R] (s : S)

open AddSubmonoidClass

/- Prefer subclasses of `NonUnitalNonAssocSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocSemiring` inherits a
`NonUnitalNonAssocSemiring` structure -/
/-
**NonUnitalSubsemiringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiringClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring of a `NonUnitalNonAssocSemiring` inherits a
`NonUnitalNonAssocSemiring` structure
-/
instance (priority := 75) toNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalNonAssocSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/- Prefer subclasses of `NonUnitalNonAssocCommSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocCommSemiring` inherits a
`NonUnitalNonAssocCommSemiring` structure -/
/-
**NonUnitalSubsemiringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiringClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring of a `NonUnitalNonAssocCommSemiring` inherits a
`NonUnitalNonAssocCommSemiring` structure
-/
instance (priority := 75) toNonUnitalNonAssocCommSemiring {R} [NonUnitalNonAssocCommSemiring R]
    [SetLike S R] [NonUnitalSubsemiringClass S R] :
    NonUnitalNonAssocCommSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalNonAssocCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl
/-
**NonUnitalSubsemiringClass.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalS
ubsemiringClass`。
形式化陈述：noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors Subtype.val rfl fun _ _ => rfl

/-- The natural non-unital ring hom from a non-unital subsemiring of a non-unital semiring `R` to
`R`. -/
/-
**NonUnitalSubsemiringClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemir
ingClass`。
形式化陈述：subtype : s ->ₙ+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…

--- 原说明 ---
The natural non-unital ring hom from a non-unital subsemiring of a non-unital se
miring `R` to
`R`.
-/
def subtype : s →ₙ+* R :=
  { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }

variable {s} in
@[simp]
/-
**NonUnitalSubsemiringClass.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiringClass`。
形式化陈述：subtype_apply (x : s) : subtype s x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply (x : s) : subtype s x = x :=
  rfl
/-
**NonUnitalSubsemiringClass.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubsemiringClass`。
形式化陈述：subtype_injective : Function.Injective (subtype s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective : Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/-
**NonUnitalSubsemiringClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubs
emiringClass`。
形式化陈述：coe_subtype : (subtype s : s -> R) = ((↑) : s -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

/-- A non-unital subsemiring of a `NonUnitalSemiring` is a `NonUnitalSemiring`. -/
/-
**NonUnitalSubsemiringClass.toNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubsemiringClass`。
形式化陈述：toNonUnitalSemiring {R} [NonUnitalSemiring R] [SetLike S R] [NonUnitalSubs
emiringClass S R] : NonUnitalSemiring s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring of a `NonUnitalSemiring` is a `NonUnitalSemiring`.
-/
instance toNonUnitalSemiring {R} [NonUnitalSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalSemiring Subtype.val rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl

/-- A non-unital subsemiring of a `NonUnitalCommSemiring` is a `NonUnitalCommSemiring`. -/
/-
**NonUnitalSubsemiringClass.toNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalSubsemiringClass`。
形式化陈述：toNonUnitalCommSemiring {R} [NonUnitalCommSemiring R] [SetLike S R] [NonUn
italSubsemiringClass S R] : NonUnitalCommSemiring s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring of a `NonUnitalCommSemiring` is a `NonUnitalCommSemirin
g`.
-/
instance toNonUnitalCommSemiring {R} [NonUnitalCommSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalCommSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/

end NonUnitalSubsemiringClass

/-- A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is both an additive
submonoid and a semigroup. -/
/-
**NonUnitalSubsemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [NonUnitalNonAssocSemiring R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is bo
th an additive
submonoid and a semigroup.
-/
structure NonUnitalSubsemiring (R : Type u) [NonUnitalNonAssocSemiring R] extends AddSubmonoid R,
  Subsemigroup R

/-- Reinterpret a `NonUnitalSubsemiring` as a `Subsemigroup`. -/
add_decl_doc NonUnitalSubsemiring.toSubsemigroup

/-- Reinterpret a `NonUnitalSubsemiring` as an `AddSubmonoid`. -/
add_decl_doc NonUnitalSubsemiring.toAddSubmonoid

namespace NonUnitalSubsemiring

/-
**NonUnitalSubsemiring.toAddSubmonoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `NonUn
italSubsemiring`。
形式化陈述：toAddSubmonoid_injective : (toAddSubmonoid : NonUnitalSubsemiring R -> Add
Submonoid R).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `NonUnitalSubsemiring.mul_mem'`：∀ {R : Type u} [inst : NonUnitalNonAssocS
emiring R] (self : NonUnitalSubsemiring R) {a b : R},   a ∈ self.carrier → b ∈ s
elf.carrier → a * b…
-/
lemma toAddSubmonoid_injective :
    (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R).Injective :=
  fun ⟨s, hs⟩ t ↦ by congr!
/-
**NonUnitalSubsemiring.toAddSubmonoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R] {s t : NonUnitalSubsem
iring R},   s.toAddSubmonoid = t.toAddSubmonoid ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `NonUnitalSubsemiring.toAddSubmonoid_injective`：toAddSubmonoid_injective 
: (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R).Injective
-/
@[simp] lemma toAddSubmonoid_inj {s t : NonUnitalSubsemiring R} :
    s.toAddSubmonoid = t.toAddSubmonoid ↔ s = t := toAddSubmonoid_injective.eq_iff
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (NonUnitalSubsemiring R) R where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toAddSubmonoid_injective
/-
**NonUnitalSubsemiring.toSubsemigroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italSubsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R], Function.Injective No
nUnitalSubsemiring.toSubsemigroup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R)
  | _, _, h => SetLike.ext (SetLike.ext_iff.mp h :)
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonUnitalSubsemiring R) := .ofSetLike (NonUnitalSubsemiring R) R

/-- The actual `NonUnitalSubsemiring` obtained from an element of a `NonUnitalSubsemiringClass`. -/
@[simps]
/-
**NonUnitalSubsemiring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R] [NonUnit
alSubsemiringClass S R] (s : S) : NonUnitalSubsemiring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `NonUnitalSubsemiring` obtained from an element of a `NonUnitalSubsem
iringClass`.
-/
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] (s : S) : NonUnitalSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (NonUnitalSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2 },
      rfl ⟩
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R where
  zero_mem {s} := AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s
/-
**NonUnitalSubsemiring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：mem_carrier {s : NonUnitalSubsemiring R} {x : R} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two non-unital subsemirings are equal if they have the same elements. -/
@[ext]
/-
**NonUnitalSubsemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：ext {S T : NonUnitalSubsemiring R} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two non-unital subsemirings are equal if they have the same elements.
-/
theorem ext {S T : NonUnitalSubsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital subsemiring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**NonUnitalSubsemiring.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：{R : Type u} →   [inst : NonUnitalNonAssocSemiring R] → (S : NonUnitalSubs
emiring R) → (s : Set R) → s = ↑S → NonUnitalSubsemiring R
参数：S : NonUnitalSubsemiring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital subsemiring with a new `carrier` equal to the old one. Usef
ul to fix
definitional equalities.
-/
protected def copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalSubsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }

@[simp]
/-
**NonUnitalSubsemiring.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：coe_copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy 
s hs : Set R) = s
参数：S : NonUnitalSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl
/-
**NonUnitalSubsemiring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：copy_eq (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s 
hs = S
参数：S : NonUnitalSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/-- Construct a `NonUnitalSubsemiring R` from a set `s`, a subsemigroup `sg`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sg ↔ x ∈ sa`. -/
/-
**NonUnitalSubsemiring.mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mk'_toSubsemigroup {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : 
AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toSubs
emigroup = sg
参数：hg : ↑sg = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `NonUnitalSubsemiring R` from a set `s`, a subsemigroup `sg`, and an
 additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sg ↔ x ∈ sa`.
-/
protected def mk' (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : NonUnitalSubsemiring R where
  carrier := s
  zero_mem' := by subst ha; exact sa.zero_mem
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem

@[simp]
/-
**NonUnitalSubsemiring.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoi
d R} (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha : Set R) = s
参数：hg : ↑sg = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mk'`：mk'_toSubsemigroup {s : Set R} {sg : Subsemigr
oup R} (hg : ↑sg = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiri
ng.mk' s sg hg…
-/
theorem coe_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha : Set R) = s :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mem_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoi
d R} (ha : ↑sa = s) {x : R} : x in NonUnitalSubsemiring.mk' s sg hg sa ha ↔ x in
 s
参数：hg : ↑sg = s；ha : ↑sa = s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `NonUnitalSubsemiring.mk'`：mk'_toSubsemigroup {s : Set R} {sg : Subsemigr
oup R} (hg : ↑sg = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiri
ng.mk' s sg hg…
-/
theorem mem_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) {x : R} : x ∈ NonUnitalSubsemiring.mk' s sg hg sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubsemiring.mk'_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R] {s : Set R} {sg : Subs
emigroup R} (hg : ↑sg = s)   {sa : AddSubmonoid R} (ha : ↑sa = s), (NonUnitalSub
semiring.mk' s sg hg sa ha).toSubsemigroup = sg
参数：hg : ↑sg = s；ha : ↑sa = s；NonUnitalSubsemiring.mk' s sg hg sa ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubsemiring.mk'`：mk'_toSubsemigroup {s : Set R} {sg : Subsemigr
oup R} (hg : ↑sg = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiri
ng.mk' s sg hg…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toSubsemigroup {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toSubsemigroup = sg :=
  SetLike.coe_injective hg.symm

@[simp]
/-
**NonUnitalSubsemiring.mk'_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R] {s : Set R} {sg : Subs
emigroup R} (hg : ↑sg = s)   {sa : AddSubmonoid R} (ha : ↑sa = s), (NonUnitalSub
semiring.mk' s sg hg sa ha).toAddSubmonoid = sa
参数：hg : ↑sg = s；ha : ↑sa = s；NonUnitalSubsemiring.mk' s sg hg sa ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubsemiring.mk'`：mk'_toSubsemigroup {s : Set R} {sg : Subsemigr
oup R} (hg : ↑sg = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiri
ng.mk' s sg hg…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toAddSubmonoid {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubsemiring R)

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：coe_zero : ((0 : s) : R) = (0 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_add (x y : s) : ((x + y : s) : R) = (x + y : R)
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R)
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/


@[simp high]
/-
**NonUnitalSubsemiring.mem_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：mem_toSubsemigroup {s : NonUnitalSubsemiring R} {x : R} : x in s.toSubsemi
group ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Note: currently, there are no ordered versions of non-unital rings.
-/
theorem mem_toSubsemigroup {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[simp high]
/-
**NonUnitalSubsemiring.coe_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：coe_toSubsemigroup (s : NonUnitalSubsemiring R) : (s.toSubsemigroup : Set 
R) = s
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubsemigroup (s : NonUnitalSubsemiring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：mem_toAddSubmonoid {s : NonUnitalSubsemiring R} {x : R} : x in s.toAddSubm
onoid ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubmonoid {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubsemiring.coe_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：coe_toAddSubmonoid (s : NonUnitalSubsemiring R) : (s.toAddSubmonoid : Set 
R) = s
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubmonoid (s : NonUnitalSubsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The non-unital subsemiring `R` of the non-unital semiring `R`. -/
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-unital subsemiring `R` of the non-unital semiring `R`.
-/
instance : Top (NonUnitalSubsemiring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
/-
**NonUnitalSubsemiring.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mem_top (x : R) : x in (⊤ : NonUnitalSubsemiring R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubsemiring R) :=
  Set.mem_univ x

@[simp]
/-
**NonUnitalSubsemiring.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_top : ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ :=
  rfl
/-
**NonUnitalSubsemiring.toAddSubmonoid_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R], ⊤.toAddSubmonoid = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddSubmonoid_top : (⊤ : NonUnitalSubsemiring R).toAddSubmonoid = ⊤ := rfl

@[simp]
/-
**NonUnitalSubsemiring.toAddSubmonoid_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `NonUnita
lSubsemiring`。
形式化陈述：toAddSubmonoid_eq_top {S : NonUnitalSubsemiring R} : S.toAddSubmonoid = ⊤ 
↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toAddSubmonoid_eq_top {S : NonUnitalSubsemiring R} : S.toAddSubmonoid = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

-- should we define this as the range of the zero homomorphism?
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (NonUnitalSubsemiring R) :=
  ⟨{  carrier := {0}
      add_mem' := fun _ _ => by simp_all
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NonUnitalSubsemiring R) :=
  ⟨⊥⟩
/-
**NonUnitalSubsemiring.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_bot : ((⊥ : NonUnitalSubsemiring R) : Set R) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : NonUnitalSubsemiring R) : Set R) = {0} :=
  rfl
/-
**NonUnitalSubsemiring.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mem_bot {x : R} : x in (⊥ : NonUnitalSubsemiring R) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubsemiring R) ↔ x = 0 :=
  Set.mem_singleton_iff

/-- The inf of two non-unital subsemirings is their intersection. -/
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two non-unital subsemirings is their intersection.
-/
instance : Min (NonUnitalSubsemiring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s ∩ t }⟩

@[simp]
/-
**NonUnitalSubsemiring.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_inf (p p' : NonUnitalSubsemiring R) : ((p ⊓ p' : NonUnitalSubsemiring 
R) : Set R) = (p : Set R) inter p'
参数：p p' : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : NonUnitalSubsemiring R) :
    ((p ⊓ p' : NonUnitalSubsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mem_inf {p p' : NonUnitalSubsemiring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x
 in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : NonUnitalSubsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [FunLike F R S]

variable [NonUnitalNonAssocSemiring S]
  [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/-- Restriction of a non-unital ring homomorphism to a non-unital subsemiring of the codomain. -/
/-
**NonUnitalRingHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：codRestrict (f : F) (s : S') (h : forall x, f x in s) : R ->ₙ+* s where to
Fun n
参数：f : F；s : S'；h : forall x, f x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a non-unital ring homomorphism to a non-unital subsemiring of the
 codomain.
-/
def codRestrict (f : F) (s : S') (h : ∀ x, f x ∈ s) : R →ₙ+* s where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_add' x y := Subtype.ext (map_add f x y)
  map_zero' := Subtype.ext (map_zero f)

/-- The non-unital subsemiring of elements `x : R` such that `f x = g x` -/
/-
**NonUnitalRingHom.eqSlocus** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：eqSlocus (f g : F) : NonUnitalSubsemiring R
参数：f g : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…

--- 原说明 ---
The non-unital subsemiring of elements `x : R` such that `f x = g x`
-/
def eqSlocus (f g : F) : NonUnitalSubsemiring R :=
  { (f : R →ₙ* S).eqLocus (g : R →ₙ* S), (f : R →+ S).eqLocusM g with
    carrier := { x | f x = g x } }

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

/-- The non-unital ring homomorphism associated to an inclusion of
non-unital subsemirings. -/
/-
**NonUnitalSubsemiring.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：inclusion {S T : NonUnitalSubsemiring R} (h : S <= T) : S ->ₙ+* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
The non-unital ring homomorphism associated to an inclusion of
non-unital subsemirings.
-/
def inclusion {S T : NonUnitalSubsemiring R} (h : S ≤ T) : S →ₙ+* T :=
  codRestrict (subtype S) _ fun x => h x.2

end NonUnitalSubsemiring

