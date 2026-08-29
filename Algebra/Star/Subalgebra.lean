/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Star subalgebras

A \*-subalgebra is a subalgebra of a \*-algebra which is closed under `*`.

The centralizer of a \*-closed set is a \*-subalgebra.
-/

@[expose] public section

universe u v

/--
Definition of `StarSubalgebra` / `StarSubalgebra` 的定义

English:
structure StarSubalgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
  extends: Subalgebra R A
  axioms and operations (1):
    - star_mem'({a}) : a in carrier -> star a in carrier

中文:
结构 对合子代数
  参数: (R : 类型u) (A : 类型v) [交换半环 R] [对合环 R] [半环 A]
  继承: 子代数 R A
  公理与运算 (1 个):
    - star_mem'({a}) : a in carrier -> star a in carrier
-/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
    [StarRing A] [Algebra R A] [StarModule R A] : Type v extends Subalgebra R A where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a in carrier -> star a in carrier

namespace StarSubalgebra

/-- Forgetting that a \*-subalgebra is closed under \*.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (StarSubalgebra R A) A where
  body: S.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

中文:
实例 setLike
  签名: : 集合状 (对合子代数 R A) A where
  定义体: S.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

Depends on / 依赖: S.carrier, carrier
-/
instance setLike : SetLike (StarSubalgebra R A) A where
  coe S := S.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (StarSubalgebra R A)
  body: .ofSetLike (StarSubalgebra R A) A

中文:
实例 :
  签名: 偏序 (对合子代数 R A)
  定义体: .ofSetLike (StarSubalgebra R A) A

Depends on / 依赖: StarSubalgebra, ofSetLike
-/
instance : PartialOrder (StarSubalgebra R A) := .ofSetLike (StarSubalgebra R A) A

/-- The actual `StarSubalgebra` obtained from an element of a type satisfying `SubsemiringClass`,
`SMulMemClass` and `StarMemClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R] [StarRing A]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' := algebraMap_mem s
  star_mem' := star_mem

中文:
定义 ofClass
  签名: {S R A : 类型} [交换半环 R] [半环 A] [代数 R A] [对合环 R] [对合环 A]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' := algebraMap_mem s
  star_mem' := star_mem
-/
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R] [StarRing A]
    [StarModule R A] [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) : StarSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' := algebraMap_mem s
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set A) (StarSubalgebra R A) (↑)
    (fun s => (forall {x y}, x in s -> y in s -> x + y in s) ∧ (forall {x y}, x in s -> y in s -> x * y in s) ∧
      (forall (r : R), algebraMap R A r in s) ∧ forall {x}, x in s -> star x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2.1 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2.1 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩

/--
Instance `starMemClass` / 实例 `starMemClass`

English:
instance starMemClass
  signature: : StarMemClass (StarSubalgebra R A) A where
  body: s.star_mem'

中文:
实例 starMemClass
  签名: : StarMem类 (对合子代数 R A) A where
  定义体: s.star_mem'

Depends on / 依赖: s.star_mem, star_mem
-/
instance starMemClass : StarMemClass (StarSubalgebra R A) A where
  star_mem {s} := s.star_mem'


/--
Instance `subsemiringClass` / 实例 `subsemiringClass`

English:
instance subsemiringClass
  signature: : SubsemiringClass (StarSubalgebra R A) A where
  body: s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'

中文:
实例 subsemiringClass
  签名: : 子半环类 (对合子代数 R A) A where
  定义体: s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'

Depends on / 依赖: add_mem, s.add_mem
-/
instance subsemiringClass : SubsemiringClass (StarSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'

/--
Instance `smulMemClass` / 实例 `smulMemClass`

English:
instance smulMemClass
  signature: : SMulMemClass (StarSubalgebra R A) R A where
  body: (SMulMemClass.smul_mem r ha : r • a in s.toSubalgebra)

中文:
实例 smulMemClass
  签名: : SMulMem类 (对合子代数 R A) R A where
  定义体: (SMulMemClass.smul_mem r ha : r • a in s.toSubalgebra)

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, s.toSubalgebra, smul_mem, toSubalgebra
-/
instance smulMemClass : SMulMemClass (StarSubalgebra R A) R A where
  smul_mem {s} r a (ha : a in s.toSubalgebra) :=
    (SMulMemClass.smul_mem r ha : r • a in s.toSubalgebra)

/--
Instance `subringClass` / 实例 `subringClass`

English:
instance subringClass
  signature: {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  body: show -a in s.toSubalgebra from neg_mem ha

中文:
实例 subringClass
  签名: {R A} [交换环 R] [对合环 R] [环 A] [对合环 A] [代数 R A]
  定义体: show -a in s.toSubalgebra from neg_mem ha

Depends on / 依赖: neg_mem, s.toSubalgebra, toSubalgebra
-/
instance subringClass {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
    [StarModule R A] : SubringClass (StarSubalgebra R A) A where
  neg_mem {s a} ha := show -a in s.toSubalgebra from neg_mem ha

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubalgebra R A) A`
/--
Instance `starRing` / 实例 `starRing`

English:
instance starRing
  signature: (s : StarSubalgebra R A)
  body: { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : A))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : A) (r₂ : A))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : A) (r₂ : A)) }

中文:
实例 starRing
  签名: (s : 对合子代数 R A)
  定义体: { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : A))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : A) (r₂ : A))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : A) (r₂ : A)) }

Depends on / 依赖: StarMemClass, StarMemClass.instStar, Subtype, Subtype.ext, instStar, star_add, star_involutive, star_mul, star_star
-/
instance starRing (s : StarSubalgebra R A) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : A))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : A) (r₂ : A))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : A) (r₂ : A)) }

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: (s : StarSubalgebra R A)
  body: s.toSubalgebra.algebra'

中文:
实例 algebra
  签名: (s : 对合子代数 R A)
  定义体: s.toSubalgebra.algebra'

Depends on / 依赖: algebra, s.toSubalgebra.algebra, toSubalgebra
-/
instance algebra (s : StarSubalgebra R A) : Algebra R s :=
  s.toSubalgebra.algebra'

/--
Instance `starModule` / 实例 `starModule`

English:
instance starModule
  signature: (s : StarSubalgebra R A)
  body: Subtype.ext (star_smul r (a : A))

中文:
实例 starModule
  签名: (s : 对合子代数 R A)
  定义体: Subtype.ext (star_smul r (a : A))

Depends on / 依赖: Subtype, Subtype.ext, star_smul
-/
instance starModule (s : StarSubalgebra R A) : StarModule R s where
  star_smul r a := Subtype.ext (star_smul r (a : A))

/-- Turn a `StarSubalgebra` into a `NonUnitalStarSubalgebra` by forgetting that it contains `1`. -/
@[reducible]
/--
Definition of `toNonUnitalStarSubalgebra` / `toNonUnitalStarSubalgebra` 的定义

English:
definition toNonUnitalStarSubalgebra
  signature: (S : StarSubalgebra R A)
  body: S
  smul_mem' r _x hx := S.smul_mem hx r

中文:
定义 toNonUnitalStarSubalgebra
  签名: (S : 对合子代数 R A)
  定义体: S
  smul_mem' r _x hx := S.smul_mem hx r
-/
def toNonUnitalStarSubalgebra (S : StarSubalgebra R A) : NonUnitalStarSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r

/--
lemma `one_mem_toNonUnitalStarSubalgebra` / 引理 `one_mem_toNonUnitalStarSubalgebra`

English:
lemma one_mem_toNonUnitalStarSubalgebra
  given: (S : StarSubalgebra R A)
  proof: S.one_mem'

@[simp]

中文:
引理 one_mem_toNonUnitalStarSubalgebra
  条件: (S : 对合子代数 R A)
  证明: S.one_mem'

@[simp]

Depends on / 依赖: S.one_mem, one_mem
-/
lemma one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    1 in S.toNonUnitalStarSubalgebra := S.one_mem'

@[simp]
/--
lemma `mem_toNonUnitalStarSubalgebra` / 引理 `mem_toNonUnitalStarSubalgebra`

English:
lemma mem_toNonUnitalStarSubalgebra
  given: {S : StarSubalgebra R A} {x : A}
  proof: Iff.rfl

中文:
引理 mem_toNonUnitalStarSubalgebra
  条件: {S : 对合子代数 R A} {x : A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_toNonUnitalStarSubalgebra {S : StarSubalgebra R A} {x : A} :
    x in S.toNonUnitalStarSubalgebra ↔ x in S :=
  Iff.rfl

/--
lemma `toNonUnitalStarSubalgebra_injective` / 引理 `toNonUnitalStarSubalgebra_injective`

English:
lemma toNonUnitalStarSubalgebra_injective
  statement: Function.Injective
  proof: fun _ _ => by simp [SetLike.ext_iff]

中文:
引理 toNonUnitalStarSubalgebra_injective
  结论: 函数.单射
  证明: fun _ _ => by simp [SetLike.ext_iff]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
lemma toNonUnitalStarSubalgebra_injective : Function.Injective
    (toNonUnitalStarSubalgebra : StarSubalgebra R A -> NonUnitalStarSubalgebra R A) :=
  fun _ _ => by simp [SetLike.ext_iff]

/--
lemma `toNonUnitalStarSubalgebra_inj` / 引理 `toNonUnitalStarSubalgebra_inj`

English:
lemma toNonUnitalStarSubalgebra_inj
  given: {S U : StarSubalgebra R A}
  proof: toNonUnitalStarSubalgebra_injective.eq_iff

中文:
引理 toNonUnitalStarSubalgebra_inj
  条件: {S U : 对合子代数 R A}
  证明: toNonUnitalStarSubalgebra_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalStarSubalgebra_injective, toNonUnitalStarSubalgebra_injective.eq_iff
-/
lemma toNonUnitalStarSubalgebra_inj {S U : StarSubalgebra R A} :
    S.toNonUnitalStarSubalgebra = U.toNonUnitalStarSubalgebra ↔ S = U :=
  toNonUnitalStarSubalgebra_injective.eq_iff

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : StarSubalgebra R A} {x : A}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[ext]

中文:
定理 mem_carrier
  条件: {s : 对合子代数 R A} {x : A}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : StarSubalgebra R A} (h : forall x : A, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : 对合子代数 R A} (h : 对任意 x : A, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : StarSubalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (S : Subalgebra R A) (h)
  statement: ((⟨S, h⟩ : StarSubalgebra R A) : Set A) = S
  proof: rfl

@[simp]

中文:
引理 coe_mk
  条件: (S : 子代数 R A) (h)
  结论: ((⟨S, h⟩ : 对合子代数 R A) : 集合 A) = S
  证明: rfl

@[simp]
-/
lemma coe_mk (S : Subalgebra R A) (h) : ((⟨S, h⟩ : StarSubalgebra R A) : Set A) = S := rfl

@[simp]
/--
theorem `mem_toSubalgebra` / 定理 `mem_toSubalgebra`

English:
theorem mem_toSubalgebra
  given: {S : StarSubalgebra R A} {x}
  statement: x in S.toSubalgebra ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubalgebra
  条件: {S : 对合子代数 R A} {x}
  结论: x in S.toSubalgebra ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubalgebra {S : StarSubalgebra R A} {x} : x in S.toSubalgebra ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubalgebra` / 定理 `coe_toSubalgebra`

English:
theorem coe_toSubalgebra
  given: (S : StarSubalgebra R A)
  statement: (S.toSubalgebra : Set A) = S
  proof: rfl

中文:
定理 coe_toSubalgebra
  条件: (S : 对合子代数 R A)
  结论: (S.toSubalgebra : 集合 A) = S
  证明: rfl
-/
theorem coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl

/--
theorem `toSubalgebra_injective` / 定理 `toSubalgebra_injective`

English:
theorem toSubalgebra_injective
  proof: fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]

中文:
定理 toSubalgebra_injective
  证明: fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]
-/
theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A -> Subalgebra R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]

/--
theorem `toSubalgebra_inj` / 定理 `toSubalgebra_inj`

English:
theorem toSubalgebra_inj
  given: {S U : StarSubalgebra R A}
  statement: S.toSubalgebra = U.toSubalgebra ↔ S = U
  proof: toSubalgebra_injective.eq_iff

中文:
定理 toSubalgebra_inj
  条件: {S U : 对合子代数 R A}
  结论: S.toSubalgebra = U.toSubalgebra ↔ S = U
  证明: toSubalgebra_injective.eq_iff

Depends on / 依赖: eq_iff, toSubalgebra_injective, toSubalgebra_injective.eq_iff
-/
theorem toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff

/--
theorem `toSubalgebra_le_iff` / 定理 `toSubalgebra_le_iff`

English:
theorem toSubalgebra_le_iff
  given: {S₁ S₂ : StarSubalgebra R A}
  proof: Iff.rfl

中文:
定理 toSubalgebra_le_iff
  条件: {S₁ S₂ : 对合子代数 R A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra <= S₂.toSubalgebra ↔ S₁ <= S₂ :=
  Iff.rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  body: Subalgebra.copy S.toSubalgebra s hs
  star_mem' {a} ha := hs ▸ S.star_mem' (by simpa [hs] using ha)

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : 对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  定义体: Subalgebra.copy S.toSubalgebra s hs
  star_mem' {a} ha := hs ▸ S.star_mem' (by simpa [hs] using ha)

@[simp, norm_cast]
-/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.copy S.toSubalgebra s hs
  star_mem' {a} ha := hs ▸ S.star_mem' (by simpa [hs] using ha)

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  statement: (S.copy s hs : Set A) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (S : 对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  结论: (S.copy s hs : 集合 A) = s
  证明: rfl
-/
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : StarSubalgebra R A)

/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (r : R)
  statement: algebraMap R A r in S
  proof: S.algebraMap_mem' r

中文:
定理 algebraMap_mem
  条件: (r : R)
  结论: algebraMap R A r in S
  证明: S.algebraMap_mem' r
-/
protected theorem algebraMap_mem (r : R) : algebraMap R A r in S :=
  S.algebraMap_mem' r

/--
theorem `rangeS_le` / 定理 `rangeS_le`

English:
theorem rangeS_le
  statement: (algebraMap R A).rangeS <= S.toSubalgebra.toSubsemiring
  proof: fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

中文:
定理 rangeS_le
  结论: (algebraMap R A).rangeS <= S.toSubalgebra.toSubsemiring
  证明: fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
-/
theorem rangeS_le : (algebraMap R A).rangeS <= S.toSubalgebra.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

/--
theorem `range_subset` / 定理 `range_subset`

English:
theorem range_subset
  statement: Set.range (algebraMap R A) subseteq S
  proof: fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

中文:
定理 range_subset
  结论: 集合.range (algebraMap R A) subseteq S
  证明: fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

Depends on / 依赖: S.algebraMap_mem, algebraMap_mem
-/
theorem range_subset : Set.range (algebraMap R A) subseteq S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

/--
theorem `range_le` / 定理 `range_le`

English:
theorem range_le
  statement: Set.range (algebraMap R A) <= S
  proof: S.range_subset

中文:
定理 range_le
  结论: 集合.range (algebraMap R A) <= S
  证明: S.range_subset

Depends on / 依赖: S.range_subset, range_subset
-/
theorem range_le : Set.range (algebraMap R A) <= S :=
  S.range_subset

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: {x : A} (hx : x in S) (r : R)
  statement: r • x in S
  proof: (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx

中文:
定理 smul_mem
  条件: {x : A} (hx : x in S) (r : R)
  结论: r • x in S
  证明: (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx
-/
protected theorem smul_mem {x : A} (hx : x in S) (r : R) : r • x in S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S ->⋆ₐ[R] A where
  body: ((↑) : S -> A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]

中文:
定义 subtype
  签名: : S ->⋆ₐ[R] A where
  定义体: ((↑) : S -> A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
-/
def subtype : S ->⋆ₐ[R] A where
  toFun := ((↑) : S -> A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (S.subtype : S -> A) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (S.subtype : S -> A) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : (S.subtype : S -> A) = Subtype.val :=
  rfl

/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: (x : S)
  statement: S.subtype x = (x : A)
  proof: rfl

@[simp]

中文:
定理 subtype_apply
  条件: (x : S)
  结论: S.subtype x = (x : A)
  证明: rfl

@[simp]
-/
theorem subtype_apply (x : S) : S.subtype x = (x : A) :=
  rfl

@[simp]
/--
theorem `toSubalgebra_subtype` / 定理 `toSubalgebra_subtype`

English:
theorem toSubalgebra_subtype
  statement: S.toSubalgebra.val = S.subtype.toAlgHom
  proof: rfl

中文:
定理 toSubalgebra_subtype
  结论: S.toSubalgebra.val = S.subtype.toAlgHom
  证明: rfl
-/
theorem toSubalgebra_subtype : S.toSubalgebra.val = S.subtype.toAlgHom :=
  rfl

/-- The inclusion map between `StarSubalgebra`s given by `Subtype.map id` as a `StarAlgHom`. -/
@[simps]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
  body: Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

中文:
定义 inclusion
  签名: {S₁ S₂ : 对合子代数 R A} (h : S₁ <= S₂)
  定义体: Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

Depends on / 依赖: Subtype, Subtype.map
-/
def inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) : S₁ ->⋆ₐ[R] S₂ where
  toFun := Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
  proof: Set.inclusion_injective h

@[simp]

中文:
定理 inclusion_injective
  条件: {S₁ S₂ : 对合子代数 R A} (h : S₁ <= S₂)
  证明: Set.inclusion_injective h

@[simp]

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) :
Function.Injective inclusion h :=
  Set.inclusion_injective h

@[simp]
/--
theorem `subtype_comp_inclusion` / 定理 `subtype_comp_inclusion`

English:
theorem subtype_comp_inclusion
  given: {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
  proof: rfl

中文:
定理 subtype_comp_inclusion
  条件: {S₁ S₂ : 对合子代数 R A} (h : S₁ <= S₂)
  证明: rfl
-/
theorem subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) :
    S₂.subtype.comp (inclusion h) = S₁.subtype :=
  rfl

section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R A)
  body: { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }

中文:
定义 map
  签名: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R A)
  定义体: { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }

Depends on / 依赖: S.star_mem, S.toSubalgebra.map, Set.mem_image_of_mem, f.toAlgHom, map_star, mem_image_of_mem, star_mem, toAlgHom, toSubalgebra
-/
def map (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }

/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {S₁ S₂ : StarSubalgebra R A} {f : A ->⋆ₐ[R] B}
  statement: S₁ <= S₂ -> S₁.map f <= S₂.map f
  proof: Set.image_mono

中文:
定理 map_mono
  条件: {S₁ S₂ : 对合子代数 R A} {f : A ->⋆ₐ[R] B}
  结论: S₁ <= S₂ -> S₁.map f <= S₂.map f
  证明: Set.image_mono

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} : S₁ <= S₂ -> S₁.map f <= S₂.map f :=
  Set.image_mono

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : A ->⋆ₐ[R] B} (hf : Function.Injective f)
  statement: Function.Injective (map f)
  proof: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

中文:
定理 map_injective
  条件: {f : A ->⋆ₐ[R] B} (hf : 函数.单射 f)
  结论: 函数.单射 (map f)
  证明: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

Depends on / 依赖: Set.ext, Set.ext_iff, Set.image_injective, SetLike, SetLike.ext_iff.mp, ext_iff, image_injective
-/
theorem map_injective {f : A ->⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : StarSubalgebra R A)
  statement: S.map (StarAlgHom.id R A) = S
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (S : 对合子代数 R A)
  结论: S.map (StarAlg态射.id R A) = S
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (S : StarSubalgebra R A) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B)
  proof: SetLike.coe_injective Set.image_image _ _ _

@[simp]

中文:
定理 map_map
  条件: (S : 对合子代数 R A) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B)
  证明: SetLike.coe_injective Set.image_image _ _ _

@[simp]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (S : StarSubalgebra R A) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {y : B}
  proof: Subsemiring.mem_map

中文:
定理 mem_map
  条件: {S : 对合子代数 R A} {f : A ->⋆ₐ[R] B} {y : B}
  证明: Subsemiring.mem_map

Depends on / 依赖: Subsemiring, Subsemiring.mem_map, mem_map
-/
theorem mem_map {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {y : B} :
    y in map f S ↔ exists x in S, f x = y :=
  Subsemiring.mem_map

/--
theorem `map_toSubalgebra` / 定理 `map_toSubalgebra`

English:
theorem map_toSubalgebra
  given: {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B}
  proof: SetLike.coe_injective rfl

@[simp, norm_cast]

中文:
定理 map_toSubalgebra
  条件: {S : 对合子代数 R A} {f : A ->⋆ₐ[R] B}
  证明: SetLike.coe_injective rfl

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toSubalgebra {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (S : StarSubalgebra R A) (f : A ->⋆ₐ[R] B)
  statement: (S.map f : Set B) = f '' S
  proof: rfl

中文:
定理 coe_map
  条件: (S : 对合子代数 R A) (f : A ->⋆ₐ[R] B)
  结论: (S.map f : 集合 B) = f '' S
  证明: rfl
-/
theorem coe_map (S : StarSubalgebra R A) (f : A ->⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B)
  body: { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) in S from (map_star f a).symm ▸ star_mem ha }

中文:
定义 comap
  签名: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R B)
  定义体: { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) in S from (map_star f a).symm ▸ star_mem ha }

Depends on / 依赖: S.toSubalgebra.comap, f.toAlgHom, map_star, star_mem, toAlgHom, toSubalgebra
-/
def comap (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) in S from (map_star f a).symm ▸ star_mem ha }

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {U : StarSubalgebra R B}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {S : 对合子代数 R A} {f : A ->⋆ₐ[R] B} {U : 对合子代数 R B}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A ->⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S <= U ↔ S <= comap f U :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : A ->⋆ₐ[R] B)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _S _U =>
  map_le_iff_le_comap

@[gcongr]

中文:
定理 gc_map_comap
  条件: (f : A ->⋆ₐ[R] B)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _S _U =>
  map_le_iff_le_comap

@[gcongr]
-/
theorem gc_map_comap (f : A ->⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U =>
  map_le_iff_le_comap

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {S₁ S₂ : StarSubalgebra R B} {f : A ->⋆ₐ[R] B}
  proof: Set.preimage_mono

中文:
定理 comap_mono
  条件: {S₁ S₂ : 对合子代数 R B} {f : A ->⋆ₐ[R] B}
  证明: Set.preimage_mono

Depends on / 依赖: Set.preimage_mono, preimage_mono
-/
theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A ->⋆ₐ[R] B} :
    S₁ <= S₂ -> S₁.comap f <= S₂.comap f :=
  Set.preimage_mono

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: {f : A ->⋆ₐ[R] B} (hf : Function.Surjective f)
  proof: fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]

中文:
定理 comap_injective
  条件: {f : A ->⋆ₐ[R] B} (hf : 函数.满射 f)
  证明: fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]
-/
theorem comap_injective {f : A ->⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (S : StarSubalgebra R A)
  statement: S.comap (StarAlgHom.id R A) = S
  proof: SetLike.coe_injective Set.preimage_id

中文:
定理 comap_id
  条件: (S : 对合子代数 R A)
  结论: S.comap (StarAlg态射.id R A) = S
  证明: SetLike.coe_injective Set.preimage_id

Depends on / 依赖: Set.preimage_id, SetLike, SetLike.coe_injective, coe_injective, preimage_id
-/
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
SetLike.coe_injective Set.preimage_id

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (S : StarSubalgebra R C) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B)
  proof: SetLike.coe_injective by exact Set.preimage_preimage

@[simp]

中文:
定理 comap_comap
  条件: (S : 对合子代数 R C) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B)
  证明: SetLike.coe_injective by exact Set.preimage_preimage

@[simp]

Depends on / 依赖: Set.preimage_preimage, SetLike, SetLike.coe_injective, coe_injective, preimage_preimage
-/
theorem comap_comap (S : StarSubalgebra R C) (g : B ->⋆ₐ[R] C) (f : A ->⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
SetLike.coe_injective by exact Set.preimage_preimage

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B) (x : A)
  statement: x in S.comap f ↔ f x in S
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_comap
  条件: (S : 对合子代数 R B) (f : A ->⋆ₐ[R] B) (x : A)
  结论: x in S.comap f ↔ f x in S
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B) (x : A) : x in S.comap f ↔ f x in S :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B)
  proof: rfl

中文:
定理 coe_comap
  条件: (S : 对合子代数 R B) (f : A ->⋆ₐ[R] B)
  证明: rfl
-/
theorem coe_comap (S : StarSubalgebra R B) (f : A ->⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

end Map

section Centralizer

variable (R)

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set A)
  body: Subalgebra.centralizer R (s union star s)
  star_mem' := Set.star_mem_centralizer

@[simp, norm_cast]

中文:
定义 centralizer
  签名: (s : 集合 A)
  定义体: Subalgebra.centralizer R (s union star s)
  star_mem' := Set.star_mem_centralizer

@[simp, norm_cast]

Depends on / 依赖: Subalgebra, Subalgebra.centralizer, centralizer
-/
def centralizer (s : Set A) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.centralizer R (s union star s)
  star_mem' := Set.star_mem_centralizer

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: (s : Set A)
  statement: (centralizer R s : Set A) = (s union star s).centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: (s : 集合 A)
  结论: (centralizer R s : 集合 A) = (s union star s).centralizer
  证明: rfl
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s union star s).centralizer :=
  rfl

open Set in
nonrec theorem mem_centralizer_iff {s : Set A} {z : A} :
    z in centralizer R s ↔ forall g in s, g * z = z * g ∧ star g * z = z * star g := by
  simp [← SetLike.mem_coe, centralizer_union, ← image_star, mem_centralizer_iff, forall_and]

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (s t : Set A) (h : s subseteq t)
  statement: centralizer R t <= centralizer R s
  proof: Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

中文:
定理 centralizer_le
  条件: (s t : 集合 A) (h : s subseteq t)
  结论: centralizer R t <= centralizer R s
  证明: Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

Depends on / 依赖: Set.centralizer_subset, Set.preimage_mono, Set.union_subset_union, centralizer_subset, preimage_mono, union_subset_union
-/
theorem centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

/--
theorem `centralizer_toSubalgebra` / 定理 `centralizer_toSubalgebra`

English:
theorem centralizer_toSubalgebra
  given: (s : Set A)
  proof: rfl

中文:
定理 centralizer_toSubalgebra
  条件: (s : 集合 A)
  证明: rfl
-/
theorem centralizer_toSubalgebra (s : Set A) :
    (centralizer R s).toSubalgebra = Subalgebra.centralizer R (s union star s) :=
  rfl

/--
theorem `coe_centralizer_centralizer` / 定理 `coe_centralizer_centralizer`

English:
theorem coe_centralizer_centralizer
  given: (s : Set A)
  proof: by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

中文:
定理 coe_centralizer_centralizer
  条件: (s : 集合 A)
  证明: by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

Depends on / 依赖: Set.union_self, StarMemClass, StarMemClass.star_coe_eq, coe_centralizer, star_coe_eq, union_self
-/
theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s union star s).centralizer.centralizer := by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

end Centralizer

end StarSubalgebra

/-! ### The star closure of a subalgebra -/
namespace Subalgebra

open scoped Pointwise

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/--
Instance `involutiveStar` / 实例 `involutiveStar`

English:
instance involutiveStar
  signature: : InvolutiveStar (Subalgebra R A) where
  body: { carrier := star S.carrier
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) in S)
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) in S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebraMap_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) in S)⟩

@[simp]

中文:
实例 involutiveStar
  签名: : InvolutiveStar (子代数 R A) where
  定义体: { carrier := star S.carrier
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) in S)
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) in S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebraMap_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) in S)⟩

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, I.ideal, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsPreimmersion, Quotient, RingHom, RingHom.surjectiveOnStalks_of_surjective, S.carrier, Set.me, Set.mem_star, Set.mem_star.mp, Spec.map, Subalgebra, Subalgebra.mem_carrier, add_mem, algebraMap_mem, carrier, isClosedEmbedding_comap_of_surjective
-/
instance involutiveStar : InvolutiveStar (Subalgebra R A) where
  star S :=
    { carrier := star S.carrier
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) in S)
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) in S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebraMap_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) in S)⟩

@[simp]
/--
theorem `mem_star_iff` / 定理 `mem_star_iff`

English:
theorem mem_star_iff
  given: (S : Subalgebra R A) (x : A)
  statement: x in star S ↔ star x in S
  proof: Iff.rfl

中文:
定理 mem_star_iff
  条件: (S : 子代数 R A) (x : A)
  结论: x in star S ↔ star x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_star_iff (S : Subalgebra R A) (x : A) : x in star S ↔ star x in S :=
  Iff.rfl

/--
theorem `star_mem_star_iff` / 定理 `star_mem_star_iff`

English:
theorem star_mem_star_iff
  given: (S : Subalgebra R A) (x : A)
  statement: star x in star S ↔ x in S
  proof: by
  simp

@[simp]

中文:
定理 star_mem_star_iff
  条件: (S : 子代数 R A) (x : A)
  结论: star x in star S ↔ x in S
  证明: by
  simp

@[simp]
-/
theorem star_mem_star_iff (S : Subalgebra R A) (x : A) : star x in star S ↔ x in S := by
  simp

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (S : Subalgebra R A)
  statement: ((star S : Subalgebra R A) : Set A) = star (S : Set A)
  proof: rfl

中文:
定理 coe_star
  条件: (S : 子代数 R A)
  结论: ((star S : 子代数 R A) : 集合 A) = star (S : 集合 A)
  证明: rfl
-/
theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star (S : Set A) :=
  rfl

/--
theorem `star_mono` / 定理 `star_mono`

English:
theorem star_mono
  statement: Monotone (star : Subalgebra R A -> Subalgebra R A)
  proof: fun _ _ h _ hx => h hx

中文:
定理 star_mono
  结论: 递增 (star : 子代数 R A -> 子代数 R A)
  证明: fun _ _ h _ hx => h hx
-/
theorem star_mono : Monotone (star : Subalgebra R A -> Subalgebra R A) := fun _ _ h _ hx => h hx

variable (R) in
/--
theorem `star_adjoin_comm` / 定理 `star_adjoin_comm`

English:
theorem star_adjoin_comm
  given: (s : Set A)
  statement: star (Algebra.adjoin R s) = Algebra.adjoin R (star s)
  proof: have : forall t : Set A, Algebra.adjoin R (star t) <= star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

中文:
定理 star_adjoin_comm
  条件: (s : 集合 A)
  结论: star (代数.adjoin R s) = 代数.adjoin R (star s)
  证明: have : forall t : Set A, Algebra.adjoin R (star t) <= star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_le, Algebra.subset_adjoin, Subalgebra, Subalgebra.star_mono, adjoin, adjoin_le, le_antisymm, star_mono, star_star, subset_adjoin
-/
theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) :=
  have : forall t : Set A, Algebra.adjoin R (star t) <= star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

/--
Definition of `starClosure` / `starClosure` 的定义

English:
definition starClosure
  signature: (S : Subalgebra R A)
  body: S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a]; rw [star_adjoin_comm]; rw [sup_comm]
    simpa using ha

@[simp]

中文:
定义 starClosure
  签名: (S : 子代数 R A)
  定义体: S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a]; rw [star_adjoin_comm]; rw [sup_comm]
    simpa using ha

@[simp]
-/
def starClosure (S : Subalgebra R A) : StarSubalgebra R A where
  toSubalgebra := S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a]; rw [star_adjoin_comm]; rw [sup_comm]
    simpa using ha

@[simp]
/--
theorem `coe_starClosure` / 定理 `coe_starClosure`

English:
theorem coe_starClosure
  given: (S : Subalgebra R A)
  proof: rfl

@[simp]

中文:
定理 coe_starClosure
  条件: (S : 子代数 R A)
  证明: rfl

@[simp]
-/
theorem coe_starClosure (S : Subalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : Subalgebra R A) := rfl

@[simp]
/--
theorem `mem_starClosure` / 定理 `mem_starClosure`

English:
theorem mem_starClosure
  given: (S : Subalgebra R A) {x : A}
  proof: Iff.rfl

中文:
定理 mem_starClosure
  条件: (S : 子代数 R A) {x : A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_starClosure (S : Subalgebra R A) {x : A} :
    x in S.starClosure ↔ x in S ⊔ star S := Iff.rfl

/--
theorem `starClosure_toSubalgebra` / 定理 `starClosure_toSubalgebra`

English:
theorem starClosure_toSubalgebra
  given: (S : Subalgebra R A)
  proof: rfl

中文:
定理 starClosure_toSubalgebra
  条件: (S : 子代数 R A)
  证明: rfl
-/
theorem starClosure_toSubalgebra (S : Subalgebra R A) :
    S.starClosure.toSubalgebra = S ⊔ star S := rfl

/--
theorem `starClosure_le` / 定理 `starClosure_le`

English:
theorem starClosure_le
  given: {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ <= S₂.toSubalgebra)
  proof: StarSubalgebra.toSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

中文:
定理 starClosure_le
  条件: {S₁ : 子代数 R A} {S₂ : 对合子代数 R A} (h : S₁ <= S₂.toSubalgebra)
  证明: StarSubalgebra.toSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

Depends on / 依赖: StarSubalgebra, StarSubalgebra.toSubalgebra_le_iff, mem_star_iff, star_mem, star_star, sup_le, toSubalgebra_le_iff
-/
theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ <= S₂.toSubalgebra) :
    S₁.starClosure <= S₂ :=
StarSubalgebra.toSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

/--
theorem `starClosure_le_iff` / 定理 `starClosure_le_iff`

English:
theorem starClosure_le_iff
  given: {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A}
  proof: ⟨fun h => le_sup_left.trans h, starClosure_le⟩

中文:
定理 starClosure_le_iff
  条件: {S₁ : 子代数 R A} {S₂ : 对合子代数 R A}
  证明: ⟨fun h => le_sup_left.trans h, starClosure_le⟩

Depends on / 依赖: le_sup_left, le_sup_left.trans, starClosure_le
-/
theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure <= S₂ ↔ S₁ <= S₂.toSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

end Subalgebra

/-! ### The star subalgebra generated by a set -/


namespace StarAlgebra

open StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
variable (R)

/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: (s : Set A)
  body: { Algebra.adjoin R (s union star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }

中文:
定义 adjoin
  签名: (s : 集合 A)
  定义体: { Algebra.adjoin R (s union star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }

Depends on / 依赖: Algebra, Algebra.adjoin, Set.union_comm, Set.union_star, Subalgebra, Subalgebra.mem_carrier, Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm, adjoin, mem_carrier, mem_star_iff, star_adjoin_comm, star_mem, star_star, union_comm, union_star
-/
def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s union star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }

/--
theorem `adjoin_eq_starClosure_adjoin` / 定理 `adjoin_eq_starClosure_adjoin`

English:
theorem adjoin_eq_starClosure_adjoin
  given: (s : Set A)
  statement: adjoin R s = (Algebra.adjoin R s).starClosure
  proof: toSubalgebra_injective
    show Algebra.adjoin R (s union star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)

中文:
定理 adjoin_eq_starClosure_adjoin
  条件: (s : 集合 A)
  结论: adjoin R s = (代数.adjoin R s).starClosure
  证明: toSubalgebra_injective
    show Algebra.adjoin R (s union star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_union, Subalgebra, Subalgebra.star_adjoin_comm, adjoin, adjoin_union, star_adjoin_comm, toSubalgebra_injective
-/
theorem adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure :=
toSubalgebra_injective
    show Algebra.adjoin R (s union star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)

/--
theorem `adjoin_toSubalgebra` / 定理 `adjoin_toSubalgebra`

English:
theorem adjoin_toSubalgebra
  given: (s : Set A)
  proof: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
定理 adjoin_toSubalgebra
  条件: (s : 集合 A)
  证明: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
-/
theorem adjoin_toSubalgebra (s : Set A) :
    (adjoin R s).toSubalgebra = Algebra.adjoin R (s union star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_adjoin` / 定理 `subset_adjoin`

English:
theorem subset_adjoin
  given: (s : Set A)
  statement: s subseteq adjoin R s
  proof: Set.subset_union_left.trans Algebra.subset_adjoin

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
定理 subset_adjoin
  条件: (s : 集合 A)
  结论: s subseteq adjoin R s
  证明: Set.subset_union_left.trans Algebra.subset_adjoin

@[simp, aesop safe 20 (rule_sets := [SetLike])]

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.subset_union_left.trans, subset_adjoin, subset_union_left
-/
theorem subset_adjoin (s : Set A) : s subseteq adjoin R s :=
  Set.subset_union_left.trans Algebra.subset_adjoin

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `star_subset_adjoin` / 定理 `star_subset_adjoin`

English:
theorem star_subset_adjoin
  given: (s : Set A)
  statement: star s subseteq adjoin R s
  proof: Set.subset_union_right.trans Algebra.subset_adjoin

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 star_subset_adjoin
  条件: (s : 集合 A)
  结论: star s subseteq adjoin R s
  证明: Set.subset_union_right.trans Algebra.subset_adjoin

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.subset_union_right.trans, subset_adjoin, subset_union_right
-/
theorem star_subset_adjoin (s : Set A) : star s subseteq adjoin R s :=
  Set.subset_union_right.trans Algebra.subset_adjoin

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_adjoin_of_mem` / 定理 `mem_adjoin_of_mem`

English:
theorem mem_adjoin_of_mem
  given: {s : Set A} {x : A} (hx : x in s)
  statement: x in adjoin R s
  proof: subset_adjoin R s hx

@[simp]

中文:
定理 mem_adjoin_of_mem
  条件: {s : 集合 A} {x : A} (hx : x in s)
  结论: x in adjoin R s
  证明: subset_adjoin R s hx

@[simp]

Depends on / 依赖: subset_adjoin
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s := subset_adjoin R s hx

@[simp]
/--
theorem `self_mem_adjoin_singleton` / 定理 `self_mem_adjoin_singleton`

English:
theorem self_mem_adjoin_singleton
  given: (x : A)
  statement: x in adjoin R ({x} : Set A)
  proof: Algebra.subset_adjoin Set.mem_union_left _ (Set.mem_singleton x)

中文:
定理 self_mem_adjoin_singleton
  条件: (x : A)
  结论: x in adjoin R ({x} : 集合 A)
  证明: Algebra.subset_adjoin Set.mem_union_left _ (Set.mem_singleton x)

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.mem_singleton, Set.mem_union_left, mem_singleton, mem_union_left, subset_adjoin
-/
theorem self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A) :=
Algebra.subset_adjoin Set.mem_union_left _ (Set.mem_singleton x)

/--
theorem `star_self_mem_adjoin_singleton` / 定理 `star_self_mem_adjoin_singleton`

English:
theorem star_self_mem_adjoin_singleton
  given: (x : A)
  statement: star x in adjoin R ({x} : Set A)
  proof: star_mem self_mem_adjoin_singleton R x

中文:
定理 star_self_mem_adjoin_singleton
  条件: (x : A)
  结论: star x in adjoin R ({x} : 集合 A)
  证明: star_mem self_mem_adjoin_singleton R x

Depends on / 依赖: self_mem_adjoin_singleton, star_mem
-/
theorem star_self_mem_adjoin_singleton (x : A) : star x in adjoin R ({x} : Set A) :=
star_mem self_mem_adjoin_singleton R x

variable {R}

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (adjoin R : Set A -> StarSubalgebra R A) (↑)
  proof: by
  intro s S
  rw [← toSubalgebra_le_iff]; rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_le_iff]; rw [coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx)⟩

中文:
定理 gc
  结论: GaloisConnection (adjoin R : 集合 A -> 对合子代数 R A) (↑)
  证明: by
  intro s S
  rw [← toSubalgebra_le_iff]; rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_le_iff]; rw [coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx)⟩
-/
protected theorem gc : GaloisConnection (adjoin R : Set A -> StarSubalgebra R A) (↑) := by
  intro s S
  rw [← toSubalgebra_le_iff]; rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_le_iff]; rw [coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx)⟩

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (adjoin R : Set A -> StarSubalgebra R A) (↑) where
  body: (adjoin R s).copy s le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (adjoin R : 集合 A -> 对合子代数 R A) (↑) where
  定义体: (adjoin R s).copy s le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _
-/
protected def gi : GaloisInsertion (adjoin R : Set A -> StarSubalgebra R A) (↑) where
choice s hs := (adjoin R s).copy s le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _

/--
theorem `adjoin_le` / 定理 `adjoin_le`

English:
theorem adjoin_le
  given: {S : StarSubalgebra R A} {s : Set A} (hs : s subseteq S)
  statement: adjoin R s <= S
  proof: StarAlgebra.gc.l_le hs

@[simp]

中文:
定理 adjoin_le
  条件: {S : 对合子代数 R A} {s : 集合 A} (hs : s subseteq S)
  结论: adjoin R s <= S
  证明: StarAlgebra.gc.l_le hs

@[simp]

Depends on / 依赖: StarAlgebra, StarAlgebra.gc.l_le, l_le
-/
theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S :=
  StarAlgebra.gc.l_le hs

@[simp]
/--
theorem `adjoin_le_iff` / 定理 `adjoin_le_iff`

English:
theorem adjoin_le_iff
  given: {S : StarSubalgebra R A} {s : Set A}
  statement: adjoin R s <= S ↔ s subseteq S
  proof: StarAlgebra.gc _ _

@[gcongr]

中文:
定理 adjoin_le_iff
  条件: {S : 对合子代数 R A} {s : 集合 A}
  结论: adjoin R s <= S ↔ s subseteq S
  证明: StarAlgebra.gc _ _

@[gcongr]

Depends on / 依赖: StarAlgebra, StarAlgebra.gc
-/
theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s <= S ↔ s subseteq S :=
  StarAlgebra.gc _ _

@[gcongr]
/--
theorem `adjoin_mono` / 定理 `adjoin_mono`

English:
theorem adjoin_mono
  given: {s t : Set A} (H : s subseteq t)
  statement: adjoin R s <= adjoin R t
  proof: StarAlgebra.gc.monotone_l H

@[simp]

中文:
定理 adjoin_mono
  条件: {s t : 集合 A} (H : s subseteq t)
  结论: adjoin R s <= adjoin R t
  证明: StarAlgebra.gc.monotone_l H

@[simp]

Depends on / 依赖: StarAlgebra, StarAlgebra.gc.monotone_l, monotone_l
-/
theorem adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t :=
  StarAlgebra.gc.monotone_l H

@[simp]
/--
lemma `adjoin_eq` / 引理 `adjoin_eq`

English:
lemma adjoin_eq
  given: (S : StarSubalgebra R A)
  statement: adjoin R (S : Set A) = S
  proof: le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

中文:
引理 adjoin_eq
  条件: (S : 对合子代数 R A)
  结论: adjoin R (S : 集合 A) = S
  证明: le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

Depends on / 依赖: adjoin_le, le_antisymm, le_rfl, subset_adjoin
-/
lemma adjoin_eq (S : StarSubalgebra R A) : adjoin R (S : Set A) = S :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

open Submodule in
/--
lemma `adjoin_eq_span` / 引理 `adjoin_eq_span`

English:
lemma adjoin_eq_span
  given: (s : Set A)
  proof: by
  rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_eq_span]

中文:
引理 adjoin_eq_span
  条件: (s : 集合 A)
  证明: by
  rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_eq_span]

Depends on / 依赖: Algebra, Algebra.adjoin_eq_span, adjoin_eq_span, adjoin_toSubalgebra
-/
lemma adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s union star s)) := by
  rw [adjoin_toSubalgebra]; rw [Algebra.adjoin_eq_span]

open Submodule in
/--
lemma `adjoin_nonUnitalStarSubalgebra_eq_span` / 引理 `adjoin_nonUnitalStarSubalgebra_eq_span`

English:
lemma adjoin_nonUnitalStarSubalgebra_eq_span
  given: (s : NonUnitalStarSubalgebra R A)
  proof: by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalStarAlgebra.adjoin_eq_span]; rw [NonUnitalStarAlgebra.adjoin_eq]

中文:
引理 adjoin_nonUnitalStarSubalgebra_eq_span
  条件: (s : 非幺对合子代数 R A)
  证明: by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalStarAlgebra.adjoin_eq_span]; rw [NonUnitalStarAlgebra.adjoin_eq]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.adjoin_eq, NonUnitalStarAlgebra.adjoin_eq_span, Submonoid, Submonoid.closure_eq_one_union, adjoin_eq, adjoin_eq_span, closure_eq_one_union, span_union
-/
lemma adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    (adjoin R (s : Set A)).toSubalgebra.toSubmodule = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalStarAlgebra.adjoin_eq_span]; rw [NonUnitalStarAlgebra.adjoin_eq]

/--
theorem `_root_.Subalgebra.starClosure_eq_adjoin` / 定理 `_root_.Subalgebra.starClosure_eq_adjoin`

English:
theorem _root_.Subalgebra.starClosure_eq_adjoin
  given: (S : Subalgebra R A)
  proof: le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

中文:
定理 _root_.子代数.starClosure_eq_adjoin
  条件: (S : 子代数 R A)
  证明: le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

Depends on / 依赖: Subalgebra, Subalgebra.starClosure_le_iff, adjoin_le, le_antisymm, le_sup_left, starClosure_le_iff, subset_adjoin
-/
theorem _root_.Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
/--
theorem `adjoin_induction` / 定理 `adjoin_induction`

English:
theorem adjoin_induction
  statement: {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
  proof: by
  refine Algebra.adjoin_induction (fun x hx => ?_) algebraMap add mul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

@[elab_as_elim]

中文:
定理 adjoin_induction
  结论: {s : 集合 A} {p : (x : A) -> x in adjoin R s -> 命题}
  证明: by
  refine Algebra.adjoin_induction (fun x hx => ?_) algebraMap add mul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

@[elab_as_elim]

Depends on / 依赖: Algebra, Algebra.adjoin_induction, Algebra.subset_adjoin, Or.inl, adjoin_induction, algebraMap, subset_adjoin
-/
theorem adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
    (mem : forall (x) (h : x in s), p x (subset_adjoin R s h))
    (algebraMap : forall r, p (algebraMap R _ r) (algebraMap_mem _ r))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    (star : forall x hx, p x hx -> p (star x) (star_mem hx))
    {a : A} (ha : a in adjoin R s) : p a ha := by
  refine Algebra.adjoin_induction (fun x hx => ?_) algebraMap add mul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

@[elab_as_elim]
/--
theorem `adjoin_induction₂` / 定理 `adjoin_induction₂`

English:
theorem adjoin_induction₂
  statement: {s : Set A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> Prop}
  proof: by
  induction hb using adjoin_induction with
  | mem z hz => induction ha using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

中文:
定理 adjoin_induction₂
  结论: {s : 集合 A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> 命题}
  证明: by
  induction hb using adjoin_induction with
  | mem z hz => induction ha using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

Depends on / 依赖: add_left, adjoin_induction, algebraMap, algebraMap_both, algebraMap_left, algebraMap_right, mem_mem, mul_left, star_left
-/
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_adjoin R s hx)
      (subset_adjoin R s hy))
    (algebraMap_both : forall r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂)
      (algebraMap_mem _ r₁) (algebraMap_mem _ r₂))
    (algebraMap_left : forall (r) (x) (hx : x in s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (subset_adjoin R s hx))
    (algebraMap_right : forall (r) (x) (hx : x in s), p x (algebraMap R A r) (subset_adjoin R s hx)
      (algebraMap_mem _ r))
    (add_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x + y) z (add_mem hx hy) hz)
    (add_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y + z) hx (add_mem hy hz))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y * z) hx (mul_mem hy hz))
    (star_left : forall x y hx hy, p x y hx hy -> p (star x) y (star_mem hx) hy)
    (star_right : forall x y hx hy, p x y hx hy -> p x (star y) hx (star_mem hy))
    {a b : A} (ha : a in adjoin R s) (hb : b in adjoin R s) :
    p a b ha hb := by
  induction hb using adjoin_induction with
  | mem z hz => induction ha using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

/-- The difference with `StarSubalgebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim]
/--
theorem `adjoin_induction_subtype` / 定理 `adjoin_induction_subtype`

English:
theorem adjoin_induction_subtype
  statement: {s : Set A} {p : adjoin R s -> Prop} (a : adjoin R s)
  proof: Subtype.recOn a fun b hb => by
    induction hb using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

中文:
定理 adjoin_induction_subtype
  结论: {s : 集合 A} {p : adjoin R s -> 命题} (a : adjoin R s)
  证明: Subtype.recOn a fun b hb => by
    induction hb using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

Depends on / 依赖: Subtype, Subtype.recOn, adjoin_induction, algebraMap
-/
theorem adjoin_induction_subtype {s : Set A} {p : adjoin R s -> Prop} (a : adjoin R s)
    (mem : forall (x) (h : x in s), p ⟨x, subset_adjoin R s h⟩) (algebraMap : forall r, p (algebraMap R _ r))
    (add : forall x y, p x -> p y -> p (x + y)) (mul : forall x y, p x -> p y -> p (x * y))
    (star : forall x, p x -> p (star x)) : p a :=
  Subtype.recOn a fun b hb => by
    induction hb using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

variable (R)

/--
lemma `adjoin_le_centralizer_centralizer` / 引理 `adjoin_le_centralizer_centralizer`

English:
lemma adjoin_le_centralizer_centralizer
  given: (s : Set A)
  proof: by
  rw [← toSubalgebra_le_iff]; rw [centralizer_toSubalgebra]; rw [adjoin_toSubalgebra]
  convert! Algebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

中文:
引理 adjoin_le_centralizer_centralizer
  条件: (s : 集合 A)
  证明: by
  rw [← toSubalgebra_le_iff]; rw [centralizer_toSubalgebra]; rw [adjoin_toSubalgebra]
  convert! Algebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

Depends on / 依赖: Algebra, Algebra.adjoin_le_centralizer_centralizer, StarMemClass, StarMemClass.star_coe_eq, adjoin_le_centralizer_centralizer, adjoin_toSubalgebra, centralizer_toSubalgebra, convert, star_coe_eq, toSubalgebra_le_iff
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s <= centralizer R (centralizer R s) := by
  rw [← toSubalgebra_le_iff]; rw [centralizer_toSubalgebra]; rw [adjoin_toSubalgebra]
  convert! Algebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

/--
theorem `isMulCommutative_adjoin` / 定理 `isMulCommutative_adjoin`

English:
theorem isMulCommutative_adjoin
  statement: {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
  proof: by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe]; rw [coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

中文:
定理 isMulCommutative_adjoin
  结论: {s : 集合 A} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  证明: by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe]; rw [coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, Set.union_star_self_comm, SetLike, SetLike.mem_coe, adjoin_le_centralizer_centralizer, centralizer_centralizer_comm_of_comm, coe_centralizer_centralizer, hcomm_star, mem_coe, of_setLike_mul_comm, union_star_self_comm
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
    (hcomm_star : forall a in s, forall b in s, a * star b = star b * a) :
    IsMulCommutative (adjoin R s) := by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe]; rw [coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinCommSemiringOfComm` / `adjoinCommSemiringOfComm` 的定义

English:
abbreviation adjoinCommSemiringOfComm
  signature: {s : Set A}
  body: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

中文:
缩写 adjoinCommSemiringOfComm
  签名: {s : 集合 A}
  定义体: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

Depends on / 依赖: hcomm_star, isMulCommutative_adjoin
-/
abbrev adjoinCommSemiringOfComm {s : Set A}
    (hcomm : forall a in s, forall b in s, a * b = b * a)
    (hcomm_star : forall a in s, forall b in s, a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

/--
Instance `instIsMulCommutative_adjoin` / 实例 `instIsMulCommutative_adjoin`

English:
instance instIsMulCommutative_adjoin
  signature: {S : Type*} [SetLike S A] [MulMemClass S A] [StarMemClass S A]
  body: isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

中文:
实例 instIsMulCommutative_adjoin
  签名: {S : 类型} [集合状 S A] [MulMem类 S A] [StarMem类 S A]
  定义体: isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

Depends on / 依赖: isMulCommutative_adjoin, setLike_mul_comm, star_mem
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] [StarMemClass S A]
    (s : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinCommRingOfComm` / `adjoinCommRingOfComm` 的定义

English:
abbreviation adjoinCommRingOfComm
  signature: (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
  body: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

中文:
缩写 adjoinCommRingOfComm
  签名: (R : 类型u) {A : 类型v} [交换环 R] [对合环 R] [环 A]
  定义体: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

Depends on / 依赖: hcomm_star, isMulCommutative_adjoin
-/
abbrev adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : forall a : A, a in s -> forall b : A, b in s -> a * b = b * a)
    (hcomm_star : forall a : A, a in s -> forall b : A, b in s -> a * star b = star b * a) :
    CommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

/--
Instance `isMulCommutative_adjoin_singleton` / 实例 `isMulCommutative_adjoin_singleton`

English:
instance isMulCommutative_adjoin_singleton
  signature: (x : A) [IsStarNormal x]
  body: isMulCommutative_adjoin R (by grind) (by grind)

中文:
实例 isMulCommutative_adjoin_singleton
  签名: (x : A) [是StarNormal x]
  定义体: isMulCommutative_adjoin R (by grind) (by grind)

Depends on / 依赖: isMulCommutative_adjoin
-/
instance isMulCommutative_adjoin_singleton (x : A) [IsStarNormal x] :
    IsMulCommutative (adjoin R ({x} : Set A)) :=
  isMulCommutative_adjoin R (by grind) (by grind)

open scoped IsMulCommutative in
/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
@[deprecated isMulCommutative_adjoin_singleton (since := "2026-03-11")]
/--
Instance `adjoinCommSemiringOfIsStarNormal` / 实例 `adjoinCommSemiringOfIsStarNormal`

English:
instance adjoinCommSemiringOfIsStarNormal
  signature: (x : A) [IsStarNormal x]
  body: have := isMulCommutative_adjoin_singleton R x
  inferInstance

中文:
实例 adjoinCommSemiringOfIsStarNormal
  签名: (x : A) [是StarNormal x]
  定义体: have := isMulCommutative_adjoin_singleton R x
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin_singleton
-/
instance adjoinCommSemiringOfIsStarNormal (x : A) [IsStarNormal x] :
    CommSemiring (adjoin R ({x} : Set A)) :=
  have := isMulCommutative_adjoin_singleton R x
  inferInstance

open scoped IsMulCommutative in
/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
@[deprecated isMulCommutative_adjoin_singleton (since := "2026-03-11")]
/--
Instance `adjoinCommRingOfIsStarNormal` / 实例 `adjoinCommRingOfIsStarNormal`

English:
instance adjoinCommRingOfIsStarNormal
  signature: (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
  body: have := isMulCommutative_adjoin_singleton R x
  inferInstance

中文:
实例 adjoinCommRingOfIsStarNormal
  签名: (R : 类型u) {A : 类型v} [交换环 R] [对合环 R] [环 A]
  定义体: have := isMulCommutative_adjoin_singleton R x
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin_singleton
-/
instance adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNormal x] :
    CommRing (adjoin R ({x} : Set A)) :=
  have := isMulCommutative_adjoin_singleton R x
  inferInstance

end StarAlgebra

/-! ### Complete lattice structure -/

namespace StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (StarSubalgebra R A) where
  body: GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ <= S.toSubalgebra)

中文:
实例 completeLattice
  签名: : 完备格 (对合子代数 R A) where
  定义体: GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ <= S.toSubalgebra)

Depends on / 依赖: GaloisInsertion, GaloisInsertion.liftCompleteLattice, StarAlgebra, StarAlgebra.gi, liftCompleteLattice
-/
instance completeLattice : CompleteLattice (StarSubalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ <= S.toSubalgebra)

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (StarSubalgebra R A)
  body: ⟨⊤⟩

@[simp, norm_cast]

中文:
实例 inhabited
  签名: : 可居 (对合子代数 R A)
  定义体: ⟨⊤⟩

@[simp, norm_cast]
-/
instance inhabited : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: (↑(⊤ : 对合子代数 R A) : 集合 A) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : A}
  statement: x in (⊤ : StarSubalgebra R A)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: {x : A}
  结论: x in (⊤ : 对合子代数 R A)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top {x : A} : x in (⊤ : StarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/--
theorem `top_toSubalgebra` / 定理 `top_toSubalgebra`

English:
theorem top_toSubalgebra
  statement: (⊤ : StarSubalgebra R A).toSubalgebra = ⊤
  proof: by ext; simp

中文:
定理 top_toSubalgebra
  结论: (⊤ : 对合子代数 R A).toSubalgebra = ⊤
  证明: by ext; simp
-/
theorem top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤ := by ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp]
/--
theorem `toSubalgebra_eq_top` / 定理 `toSubalgebra_eq_top`

English:
theorem toSubalgebra_eq_top
  given: {S : StarSubalgebra R A}
  statement: S.toSubalgebra = ⊤ ↔ S = ⊤
  proof: StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra

中文:
定理 toSubalgebra_eq_top
  条件: {S : 对合子代数 R A}
  结论: S.toSubalgebra = ⊤ ↔ S = ⊤
  证明: StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra

Depends on / 依赖: StarSubalgebra, StarSubalgebra.toSubalgebra_injective.eq_iff, eq_iff, toSubalgebra_injective, top_toSubalgebra
-/
theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ :=
  StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : StarSubalgebra R A}
  statement: forall {x : A}, x in S -> x in S ⊔ T
  proof: have : S <= S ⊔ T := le_sup_left; (this ·)

中文:
定理 mem_sup_left
  条件: {S T : 对合子代数 R A}
  结论: 对任意 {x : A}, x in S -> x in S ⊔ T
  证明: have : S <= S ⊔ T := le_sup_left; (this ·)

Depends on / 依赖: le_sup_left
-/
theorem mem_sup_left {S T : StarSubalgebra R A} : forall {x : A}, x in S -> x in S ⊔ T :=
  have : S <= S ⊔ T := le_sup_left; (this ·)

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : StarSubalgebra R A}
  statement: forall {x : A}, x in T -> x in S ⊔ T
  proof: have : T <= S ⊔ T := le_sup_right; (this ·)

中文:
定理 mem_sup_right
  条件: {S T : 对合子代数 R A}
  结论: 对任意 {x : A}, x in T -> x in S ⊔ T
  证明: have : T <= S ⊔ T := le_sup_right; (this ·)

Depends on / 依赖: le_sup_right
-/
theorem mem_sup_right {S T : StarSubalgebra R A} : forall {x : A}, x in T -> x in S ⊔ T :=
  have : T <= S ⊔ T := le_sup_right; (this ·)

/--
theorem `mul_mem_sup` / 定理 `mul_mem_sup`

English:
theorem mul_mem_sup
  given: {S T : StarSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T)
  proof: mul_mem (mem_sup_left hx) (mem_sup_right hy)

中文:
定理 mul_mem_sup
  条件: {S T : 对合子代数 R A} {x y : A} (hx : x in S) (hy : y in T)
  证明: mul_mem (mem_sup_left hx) (mem_sup_right hy)

Depends on / 依赖: mem_sup_left, mem_sup_right, mul_mem
-/
theorem mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T) :
    x * y in S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (f : A ->⋆ₐ[R] B) (S T : StarSubalgebra R A)
  statement: map f (S ⊔ T) = map f S ⊔ map f T
  proof: (StarSubalgebra.gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (f : A ->⋆ₐ[R] B) (S T : 对合子代数 R A)
  结论: map f (S ⊔ T) = map f S ⊔ map f T
  证明: (StarSubalgebra.gc_map_comap f).l_sup

Depends on / 依赖: StarSubalgebra, StarSubalgebra.gc_map_comap, gc_map_comap, l_sup
-/
theorem map_sup (f : A ->⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
  (StarSubalgebra.gc_map_comap f).l_sup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (f : A ->⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebra R A)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

中文:
定理 map_inf
  条件: (f : A ->⋆ₐ[R] B) (hf : 函数.单射 f) (S T : 对合子代数 R A)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (f : A ->⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebra R A) :
    map f (S ⊓ T) = map f S ⊓ map f T := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (S T : StarSubalgebra R A)
  statement: (↑(S ⊓ T) : Set A) = (S : Set A) inter T
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (S T : 对合子代数 R A)
  结论: (↑(S ⊓ T) : 集合 A) = (S : 集合 A) inter T
  证明: rfl

@[simp]
-/
theorem coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) inter T :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {S T : StarSubalgebra R A} {x : A}
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: Iff.rfl

@[simp]

中文:
定理 mem_inf
  条件: {S T : 对合子代数 R A} {x : A}
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {S T : StarSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T :=
  Iff.rfl

@[simp]
/--
theorem `inf_toSubalgebra` / 定理 `inf_toSubalgebra`

English:
theorem inf_toSubalgebra
  given: (S T : StarSubalgebra R A)
  proof: by
  ext; simp

中文:
定理 inf_toSubalgebra
  条件: (S T : 对合子代数 R A)
  证明: by
  ext; simp
-/
theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra := by
  ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (StarSubalgebra R A))
  statement: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
  proof: sInf_image

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (对合子代数 R A))
  结论: (↑(sInf S) : 集合 A) = ⋂ s in S, ↑s
  证明: sInf_image

@[simp]

Depends on / 依赖: sInf_image
-/
theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s :=
  sInf_image

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (StarSubalgebra R A)} {x : A}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (对合子代数 R A)} {x : A}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_sInf, mem_coe
-/
theorem mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x in sInf S ↔ forall p in S, x in p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/--
theorem `sInf_toSubalgebra` / 定理 `sInf_toSubalgebra`

English:
theorem sInf_toSubalgebra
  given: (S : Set (StarSubalgebra R A))
  proof: SetLike.coe_injective by simp

@[simp, norm_cast]

中文:
定理 sInf_toSubalgebra
  条件: (S : 集合 (对合子代数 R A))
  证明: SetLike.coe_injective by simp

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) :=
SetLike.coe_injective by simp

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> StarSubalgebra R A}
  statement: (↑(⨅ i, S i) : Set A) = ⋂ i, S i
  proof: by
  simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 对合子代数 R A}
  结论: (↑(⨅ i, S i) : 集合 A) = ⋂ i, S i
  证明: by
  simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} {S : ι -> StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> StarSubalgebra R A} {x : A}
  proof: by simp only [iInf, mem_sInf, Set.forall_mem_range]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 对合子代数 R A} {x : A}
  证明: by simp only [iInf, mem_sInf, Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> StarSubalgebra R A} {x : A} :
    x in ⨅ i, S i ↔ forall i, x in S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : A ->⋆ₐ[R] B) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[simp]

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : A ->⋆ₐ[R] B) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[simp]

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A ->⋆ₐ[R] B) (hf : Function.Injective f)
    (s : ι -> StarSubalgebra R A) : map f (iInf s) = ⨅ (i : ι), map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[simp]
/--
theorem `iInf_toSubalgebra` / 定理 `iInf_toSubalgebra`

English:
theorem iInf_toSubalgebra
  given: {ι : Sort*} (S : ι -> StarSubalgebra R A)
  proof: SetLike.coe_injective by simp

中文:
定理 iInf_toSubalgebra
  条件: {ι : 类型层*} (S : ι -> 对合子代数 R A)
  证明: SetLike.coe_injective by simp

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toSubalgebra {ι : Sort*} (S : ι -> StarSubalgebra R A) :
    (⨅ i, S i).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
SetLike.coe_injective by simp

/--
theorem `bot_toSubalgebra` / 定理 `bot_toSubalgebra`

English:
theorem bot_toSubalgebra
  statement: (⊥ : StarSubalgebra R A).toSubalgebra = ⊥
  proof: rfl

中文:
定理 bot_toSubalgebra
  结论: (⊥ : 对合子代数 R A).toSubalgebra = ⊥
  证明: rfl
-/
theorem bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥ := rfl

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : A}
  statement: x in (⊥ : StarSubalgebra R A) ↔ x in Set.range (algebraMap R A)
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_bot
  条件: {x : A}
  结论: x in (⊥ : 对合子代数 R A) ↔ x in 集合.range (algebraMap R A)
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_bot {x : A} : x in (⊥ : StarSubalgebra R A) ↔ x in Set.range (algebraMap R A) := Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A)
  proof: rfl

中文:
定理 coe_bot
  结论: ((⊥ : 对合子代数 R A) : 集合 A) = 集合.range (algebraMap R A)
  证明: rfl
-/
theorem coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: {S : StarSubalgebra R A}
  statement: S = ⊤ ↔ forall x : A, x in S
  proof: ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

中文:
定理 eq_top_iff
  条件: {S : 对合子代数 R A}
  结论: S = ⊤ ↔ 对任意 x : A, x in S
  证明: ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

Depends on / 依赖: mem_top
-/
theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ forall x : A, x in S :=
  ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

end StarSubalgebra

namespace StarAlgHom

open StarSubalgebra StarAlgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A]
variable [Semiring B] [Algebra R B] [StarRing B]

section
variable [StarModule R A]

/--
theorem `ext_adjoin` / 定理 `ext_adjoin`

English:
theorem ext_adjoin
  statement: {s : Set A} [FunLike F (adjoin R s) B]
  proof: by
  refine DFunLike.ext f g fun a =>
    adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]

中文:
定理 ext_adjoin
  结论: {s : 集合 A} [函数状 F (adjoin R s) B]
  证明: by
  refine DFunLike.ext f g fun a =>
    adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, DFunLike, DFunLike.ext, adjoin_induction_subtype, commutes, map_add, map_mul, map_star, subset_adjoin
-/
theorem ext_adjoin {s : Set A} [FunLike F (adjoin R s) B]
    [AlgHomClass F R (adjoin R s) B] [StarHomClass F (adjoin R s) B] {f g : F}
    (h : forall x : adjoin R s, (x : A) in s -> f x = g x) : f = g := by
  refine DFunLike.ext f g fun a =>
    adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]

/--
theorem `ext_adjoin_singleton` / 定理 `ext_adjoin_singleton`

English:
theorem ext_adjoin_singleton
  statement: {a : A} [FunLike F (adjoin R ({a} : Set A)) B]
  proof: ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
Subtype.ext Set.mem_singleton_iff.mp hx).symm ▸
      h

中文:
定理 ext_adjoin_singleton
  结论: {a : A} [函数状 F (adjoin R ({a} : 集合 A)) B]
  证明: ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
Subtype.ext Set.mem_singleton_iff.mp hx).symm ▸
      h

Depends on / 依赖: Set.mem_singleton_iff.mp, Subtype, Subtype.ext, ext_adjoin, mem_singleton_iff, self_mem_adjoin_singleton
-/
theorem ext_adjoin_singleton {a : A} [FunLike F (adjoin R ({a} : Set A)) B]
    [AlgHomClass F R (adjoin R ({a} : Set A)) B] [StarHomClass F (adjoin R ({a} : Set A)) B]
    {f g : F} (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) :
    f = g :=
  ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
Subtype.ext Set.mem_singleton_iff.mp hx).symm ▸
      h

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: : StarSubalgebra R A where
  body: AlgHom.equalizer (f : A ->ₐ[R] B) g
  star_mem' {a} (ha : f a = g a) := by simpa only [← map_star] using! congrArg star ha

@[simp]

中文:
定义 equalizer
  签名: : 对合子代数 R A where
  定义体: AlgHom.equalizer (f : A ->ₐ[R] B) g
  star_mem' {a} (ha : f a = g a) := by simpa only [← map_star] using! congrArg star ha

@[simp]

Depends on / 依赖: AlgHom, AlgHom.equalizer, equalizer
-/
def equalizer : StarSubalgebra R A where
  toSubalgebra := AlgHom.equalizer (f : A ->ₐ[R] B) g
  star_mem' {a} (ha : f a = g a) := by simpa only [← map_star] using! congrArg star ha

@[simp]
/--
theorem `mem_equalizer` / 定理 `mem_equalizer`

English:
theorem mem_equalizer
  given: (x : A)
  statement: x in StarAlgHom.equalizer f g ↔ f x = g x
  proof: Iff.rfl

中文:
定理 mem_equalizer
  条件: (x : A)
  结论: x in StarAlg态射.equalizer f g ↔ f x = g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_equalizer (x : A) : x in StarAlgHom.equalizer f g ↔ f x = g x :=
  Iff.rfl

/--
theorem `adjoin_le_equalizer` / 定理 `adjoin_le_equalizer`

English:
theorem adjoin_le_equalizer
  given: {s : Set A} (h : s.EqOn f g)
  statement: adjoin R s <= StarAlgHom.equalizer f g
  proof: adjoin_le h

中文:
定理 adjoin_le_equalizer
  条件: {s : 集合 A} (h : s.EqOn f g)
  结论: adjoin R s <= StarAlg态射.equalizer f g
  证明: adjoin_le h

Depends on / 依赖: adjoin_le
-/
theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s <= StarAlgHom.equalizer f g :=
  adjoin_le h

/--
theorem `ext_of_adjoin_eq_top` / 定理 `ext_of_adjoin_eq_top`

English:
theorem ext_of_adjoin_eq_top
  given: {s : Set A} (h : adjoin R s = ⊤) ⦃f g
  statement: F⦄ (hs : s.EqOn f g) : f = g
  proof: DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs h.symm ▸ trivial

中文:
定理 ext_of_adjoin_eq_top
  条件: {s : 集合 A} (h : adjoin R s = ⊤) ⦃f g
  结论: F⦄ (hs : s.EqOn f g) : f = g
  证明: DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs h.symm ▸ trivial

Depends on / 依赖: DFunLike, DFunLike.ext, StarAlgHom, StarAlgHom.adjoin_le_equalizer, adjoin_le_equalizer, h.symm
-/
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g :=
DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs h.symm ▸ trivial


variable [StarModule R B]

/--
theorem `map_adjoin` / 定理 `map_adjoin`

English:
theorem map_adjoin
  given: (f : A ->⋆ₐ[R] B) (s : Set A)
  proof: GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

中文:
定理 map_adjoin
  条件: (f : A ->⋆ₐ[R] B) (s : 集合 A)
  证明: GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

Depends on / 依赖: GaloisConnection, GaloisConnection.l_comm_of_u_comm, Set.image_preimage, StarAlgebra, StarAlgebra.gc, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_adjoin (f : A ->⋆ₐ[R] B) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

/--
Definition of `range` / `range` 的定义

English:
definition range
  body: φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩

中文:
定义 range
  定义体: φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩
-/
protected def range
    (φ : A ->⋆ₐ[R] B) : StarSubalgebra R B where
  toSubalgebra := φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩

/--
theorem `range_eq_map_top` / 定理 `range_eq_map_top`

English:
theorem range_eq_map_top
  given: (φ : A ->⋆ₐ[R] B)
  statement: φ.range = (⊤ : StarSubalgebra R A).map φ
  proof: StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

中文:
定理 range_eq_map_top
  条件: (φ : A ->⋆ₐ[R] B)
  结论: φ.range = (⊤ : 对合子代数 R A).map φ
  证明: StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

Depends on / 依赖: StarSubalgebra, StarSubalgebra.ext
-/
theorem range_eq_map_top (φ : A ->⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).map φ :=
  StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

end

variable [StarModule R B]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x, f x in S)
  body: AlgHom.codRestrict f.toAlgHom S.toSubalgebra hf
  map_star' := fun x => Subtype.ext (map_star f x)

@[simp]

中文:
定义 codRestrict
  签名: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R B) (hf : 对任意 x, f x in S)
  定义体: AlgHom.codRestrict f.toAlgHom S.toSubalgebra hf
  map_star' := fun x => Subtype.ext (map_star f x)

@[simp]
-/
protected def codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x, f x in S) :
    A ->⋆ₐ[R] S where
  toAlgHom := AlgHom.codRestrict f.toAlgHom S.toSubalgebra hf
  map_star' := fun x => Subtype.ext (map_star f x)

@[simp]
/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x, f x in S) (x : A)
  proof: rfl

@[simp]

中文:
定理 coe_codRestrict
  条件: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R B) (hf : 对任意 x, f x in S) (x : A)
  证明: rfl

@[simp]
-/
theorem coe_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x, f x in S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  statement: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B)
  proof: StarAlgHom.ext coe_codRestrict _ S hf

中文:
定理 subtype_comp_codRestrict
  结论: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R B)
  证明: StarAlgHom.ext coe_codRestrict _ S hf

Depends on / 依赖: StarAlgHom, StarAlgHom.ext, coe_codRestrict
-/
theorem subtype_comp_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B)
    (hf : forall x : A, f x in S) : S.subtype.comp (f.codRestrict S hf) = f :=
StarAlgHom.ext coe_codRestrict _ S hf

/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x : A, f x in S)
  proof: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

中文:
定理 injective_codRestrict
  条件: (f : A ->⋆ₐ[R] B) (S : 对合子代数 R B) (hf : 对任意 x : A, f x in S)
  证明: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, congr_arg
-/
theorem injective_codRestrict (f : A ->⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : forall x : A, f x in S) :
    Function.Injective (StarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: (f : A ->⋆ₐ[R] B)
  body: StarAlgHom.codRestrict f _ fun x => ⟨x, rfl⟩

中文:
定义 rangeRestrict
  签名: (f : A ->⋆ₐ[R] B)
  定义体: StarAlgHom.codRestrict f _ fun x => ⟨x, rfl⟩

Depends on / 依赖: StarAlgHom, StarAlgHom.codRestrict, codRestrict
-/
def rangeRestrict (f : A ->⋆ₐ[R] B) : A ->⋆ₐ[R] f.range :=
  StarAlgHom.codRestrict f _ fun x => ⟨x, rfl⟩

/-- The `StarAlgEquiv` onto the range corresponding to an injective `StarAlgHom`. -/
@[simps]
/--
Definition of `_root_.StarAlgEquiv.ofInjective` / `_root_.StarAlgEquiv.ofInjective` 的定义

English:
definition _root_.StarAlgEquiv.ofInjective
  signature: (f : A ->⋆ₐ[R] B)
  body: { AlgEquiv.ofInjective f.toAlgHom hf with
    toFun := f.rangeRestrict
    map_star' := fun a => Subtype.ext (map_star f a)
    map_smul' := fun r a => Subtype.ext (map_smul f r a) }

中文:
定义 _root_.StarAlg等价.ofInjective
  签名: (f : A ->⋆ₐ[R] B)
  定义体: { AlgEquiv.ofInjective f.toAlgHom hf with
    toFun := f.rangeRestrict
    map_star' := fun a => Subtype.ext (map_star f a)
    map_smul' := fun r a => Subtype.ext (map_smul f r a) }

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Subtype, Subtype.ext, f.rangeRestrict, f.toAlgHom, map_smul, map_star, ofInjective, rangeRestrict, toAlgHom
-/
noncomputable def _root_.StarAlgEquiv.ofInjective (f : A ->⋆ₐ[R] B)
    (hf : Function.Injective f) : A ≃⋆ₐ[R] f.range :=
  { AlgEquiv.ofInjective f.toAlgHom hf with
    toFun := f.rangeRestrict
    map_star' := fun a => Subtype.ext (map_star f a)
    map_smul' := fun r a => Subtype.ext (map_smul f r a) }
end StarAlgHom


section RestrictScalars

section Equiv

variable (R : Type*) {S A B : Type*} [CommSemiring R] [CommSemiring S]
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S] [Module S A]
  [Module S B] [Module R A] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
  [Star A] [Star B]

/-- Restrict the scalar ring of a star algebra equivalence. -/
@[simps]
/--
Definition of `StarAlgEquiv.restrictScalars` / `StarAlgEquiv.restrictScalars` 的定义

English:
definition StarAlgEquiv.restrictScalars
  signature: (f : A ≃⋆ₐ[S] B)
  body: { (f : A ->ₗ[S] B).restrictScalars R, f with
    toFun := f }

中文:
定义 StarAlg等价.restrictScalars
  签名: (f : A ≃⋆ₐ[S] B)
  定义体: { (f : A ->ₗ[S] B).restrictScalars R, f with
    toFun := f }

Depends on / 依赖: restrictScalars
-/
def StarAlgEquiv.restrictScalars (f : A ≃⋆ₐ[S] B) : A ≃⋆ₐ[R] B :=
  { (f : A ->ₗ[S] B).restrictScalars R, f with
    toFun := f }

/--
theorem `StarAlgEquiv.restrictScalars_injective` / 定理 `StarAlgEquiv.restrictScalars_injective`

English:
theorem StarAlgEquiv.restrictScalars_injective
  proof: fun _ _ h => ext (DFunLike.congr_fun h ·)

@[simp]

中文:
定理 StarAlg等价.restrictScalars_injective
  证明: fun _ _ h => ext (DFunLike.congr_fun h ·)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem StarAlgEquiv.restrictScalars_injective :
    Function.Injective (StarAlgEquiv.restrictScalars R : (A ≃⋆ₐ[S] B) -> A ≃⋆ₐ[R] B) :=
  fun _ _ h => ext (DFunLike.congr_fun h ·)

@[simp]
/--
theorem `StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars` / 定理 `StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars`

English:
theorem StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars
  given: (e : A ≃⋆ₐ[S] B)
  proof: rfl

中文:
定理 StarAlg等价.toNonUnitalStarAlgHom_restrictScalars
  条件: (e : A ≃⋆ₐ[S] B)
  证明: rfl
-/
theorem StarAlgEquiv.toNonUnitalStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) :
    (e.restrictScalars R).toNonUnitalStarAlgHom = e.toNonUnitalStarAlgHom.restrictScalars R :=
  rfl

end Equiv

section Unital

variable (R : Type*) {S A B : Type*} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B]
  [Algebra R A] [Algebra R B] [IsScalarTower R S A] [IsScalarTower R S B] [Star A] [Star B]

@[simps!]
/--
Definition of `StarAlgHom.restrictScalars` / `StarAlgHom.restrictScalars` 的定义

English:
definition StarAlgHom.restrictScalars
  signature: (f : A ->⋆ₐ[S] B)
  body: f.toAlgHom.restrictScalars R
  map_star' := map_star f

中文:
定义 StarAlg态射.restrictScalars
  签名: (f : A ->⋆ₐ[S] B)
  定义体: f.toAlgHom.restrictScalars R
  map_star' := map_star f

Depends on / 依赖: f.toAlgHom.restrictScalars, restrictScalars, toAlgHom
-/
def StarAlgHom.restrictScalars (f : A ->⋆ₐ[S] B) : A ->⋆ₐ[R] B where
  toAlgHom := f.toAlgHom.restrictScalars R
  map_star' := map_star f

/--
theorem `StarAlgHom.restrictScalars_injective` / 定理 `StarAlgHom.restrictScalars_injective`

English:
theorem StarAlgHom.restrictScalars_injective
  proof: fun f g h => StarAlgHom.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

@[simp]

中文:
定理 StarAlg态射.restrictScalars_injective
  证明: fun f g h => StarAlgHom.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, StarAlgHom, StarAlgHom.ext, congr_fun, f.restrictScalars, g.restrictScalars, restrictScalars
-/
theorem StarAlgHom.restrictScalars_injective :
    Function.Injective (StarAlgHom.restrictScalars R : (A ->⋆ₐ[S] B) -> A ->⋆ₐ[R] B) :=
  fun f g h => StarAlgHom.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

@[simp]
/--
theorem `StarAlgEquiv.toStarAlgHom_restrictScalars` / 定理 `StarAlgEquiv.toStarAlgHom_restrictScalars`

English:
theorem StarAlgEquiv.toStarAlgHom_restrictScalars
  given: (e : A ≃⋆ₐ[S] B)
  proof: rfl

中文:
定理 StarAlg等价.toStarAlgHom_restrictScalars
  条件: (e : A ≃⋆ₐ[S] B)
  证明: rfl
-/
theorem StarAlgEquiv.toStarAlgHom_restrictScalars (e : A ≃⋆ₐ[S] B) :
    (e.restrictScalars R).toStarAlgHom = e.toStarAlgHom.restrictScalars R :=
  rfl

end Unital

end RestrictScalars

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

/--
Definition of `NonUnitalStarSubalgebra.toStarSubalgebra` / `NonUnitalStarSubalgebra.toStarSubalgebra` 的定义

English:
definition NonUnitalStarSubalgebra.toStarSubalgebra
  signature: (S : NonUnitalStarSubalgebra R A) (h1 : 1 in S)
  body: S
  one_mem' := h1
  algebraMap_mem' r :=
    (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1

中文:
定义 非幺对合子代数.toStarSubalgebra
  签名: (S : 非幺对合子代数 R A) (h1 : 1 in S)
  定义体: S
  one_mem' := h1
  algebraMap_mem' r :=
    (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1
-/
def NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A) (h1 : 1 in S) :
    StarSubalgebra R A where
  __ := S
  one_mem' := h1
  algebraMap_mem' r :=
    (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1

/--
lemma `StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra` / 引理 `StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra`

English:
lemma StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra
  given: (S : StarSubalgebra R A)
  proof: by cases S; rfl

中文:
引理 对合子代数.toNonUnitalStarSubalgebra_toStarSubalgebra
  条件: (S : 对合子代数 R A)
  证明: by cases S; rfl
-/
lemma StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S := by cases S; rfl

/--
lemma `NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra` / 引理 `NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra`

English:
lemma NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
  proof: by
  cases S; rfl

中文:
引理 非幺对合子代数.toStarSubalgebra_toNonUnitalStarSubalgebra
  证明: by
  cases S; rfl
-/
lemma NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) in S) :
    (S.toStarSubalgebra h1).toNonUnitalStarSubalgebra = S := by
  cases S; rfl

variable (R)

/--
lemma `NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin` / 引理 `NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin`

English:
lemma NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin
  given: (s : Set A)
  proof: adjoin_le StarAlgebra.subset_adjoin R s

中文:
引理 NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin
  条件: (s : 集合 A)
  证明: adjoin_le StarAlgebra.subset_adjoin R s

Depends on / 依赖: StarAlgebra, StarAlgebra.subset_adjoin, adjoin_le, subset_adjoin
-/
lemma NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) :
    adjoin R s <= (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra :=
adjoin_le StarAlgebra.subset_adjoin R s

/--
lemma `StarAlgebra.adjoin_nonUnitalStarSubalgebra` / 引理 `StarAlgebra.adjoin_nonUnitalStarSubalgebra`

English:
lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra
  given: (s : Set A)
  proof: le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)

中文:
引理 对合代数.adjoin_nonUnitalStarSubalgebra
  条件: (s : 集合 A)
  证明: le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin, NonUnitalStarAlgebra.subset_adjoin, adjoin_le, adjoin_le_starAlgebra_adjoin, le_antisymm, subset_adjoin
-/
lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) :
    adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)

namespace StarSubalgebra

section directed

variable {R}

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R A}
  proof: let K : StarSubalgebra R A :=
    { __ := NonUnitalStarSubalgebra.copy _ _ (NonUnitalStarSubalgebra.coe_iSup_of_directed
        (S := fun i => (S i).toNonUnitalStarSubalgebra) dir).symm
      algebraMap_mem' x :=
        let ⟨i⟩ := ‹Nonempty ι›
        Set.mem_iUnion.mpr ⟨i, algebraMap_mem (S i) x⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i)
    (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

中文:
定理 coe_iSup_of_directed
  结论: {ι : 类型} [非空 ι] {S : ι -> 对合子代数 R A}
  证明: let K : StarSubalgebra R A :=
    { __ := NonUnitalStarSubalgebra.copy _ _ (NonUnitalStarSubalgebra.coe_iSup_of_directed
        (S := fun i => (S i).toNonUnitalStarSubalgebra) dir).symm
      algebraMap_mem' x :=
        let ⟨i⟩ := ‹Nonempty ι›
        Set.mem_iUnion.mpr ⟨i, algebraMap_mem (S i) x⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i)
    (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.coe_iSup_of_directed, NonUnitalStarSubalgebra.copy, Nonempty, Set.iUnion_subset, Set.mem_iUnion.mpr, StarSubalgebra, algebraMap_mem, coe_iSup_of_directed, iSup_le, iUnion_subset, le_antisymm, le_iSup, mem_iUnion, this.symm, toNonUnitalStarSubalgebra
-/
theorem coe_iSup_of_directed {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R A}
    (dir : Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : StarSubalgebra R A :=
    { __ := NonUnitalStarSubalgebra.copy _ _ (NonUnitalStarSubalgebra.coe_iSup_of_directed
        (S := fun i => (S i).toNonUnitalStarSubalgebra) dir).symm
      algebraMap_mem' x :=
        let ⟨i⟩ := ‹Nonempty ι›
        Set.mem_iUnion.mpr ⟨i, algebraMap_mem (S i) x⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i)
    (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R A}
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subalgebra.coe_iSup_of_directed dir] using Subalgebra.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: {ι : 类型} [非空 ι] {S : ι -> 对合子代数 R A}
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subalgebra.coe_iSup_of_directed dir] using Subalgebra.isMulCommutative_iSup dir

Depends on / 依赖: SetLike, SetLike.mem_coe, Subalgebra, Subalgebra.coe_iSup_of_directed, Subalgebra.isMulCommutative_iSup, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {ι : Type*} [Nonempty ι] {S : ι -> StarSubalgebra R A}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subalgebra.coe_iSup_of_directed dir] using Subalgebra.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [非空 ι] [预序 ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o StarSubalgebra R A} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

end directed

end StarSubalgebra
