/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!

# Basic results about relative perfect closure

This file contains basic results about relative perfect closures.

## Main definitions

- `perfectClosure`: the relative perfect closure of `F` in `E`, it consists of the elements
  `x` of `E` such that there exists a natural number `n` such that `x ^ (ringExpChar F) ^ n`
  is contained in `F`, where `ringExpChar F` is the exponential characteristic of `F`.
  It is also the maximal purely inseparable subextension of `E / F` (`le_perfectClosure_iff`).

## Main results

- `le_perfectClosure_iff`: an intermediate field of `E / F` is contained in the relative perfect
  closure of `F` in `E` if and only if it is purely inseparable over `F`.

- `perfectClosure.perfectRing`, `perfectClosure.perfectField`: if `E` is a perfect field, then the
  (relative) perfect closure `perfectClosure F E` is perfect.

- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`: if `F` is of exponential
  characteristic `q`, then `F(S) / F` is a purely inseparable extension if and only if for any
  `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

@[expose] public section

open IntermediateField Module

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section perfectClosure

/-- The relative perfect closure of `F` in `E`, consists of the elements `x` of `E` such that there
exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in `F`, where
`ringExpChar F` is the exponential characteristic of `F`. It is also the maximal purely inseparable
subextension of `E / F` (`le_perfectClosure_iff`). -/
@[stacks 09HH]
/-
**perfectClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：perfectClosure : IntermediateField F E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative perfect closure of `F` in `E`, consists of the elements `x` of `E` 
such that there
exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in 
`F`, where
`ringExpChar F` is the exponential characteristic of `F`. It is also the maximal
 purely inseparable
subextension of `E / F` (`le_perfectClosure_iff`).
-/
def perfectClosure : IntermediateField F E where
  __ := have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    Subalgebra.perfectClosure F E (ringExpChar F)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ ∈ (⊥ : IntermediateField F E))

variable {F E}
/-
**mem_perfectClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_perfectClosure_iff {x : E} : x in perfectClosure F E ↔ exists n : Nat,
 x ^ (ringExpChar F) ^ n in (algebraMap F E).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_perfectClosure_iff {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := Iff.rfl
/-
**mem_perfectClosure_iff_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_perfectClosure_iff_pow_mem (q : Nat) [ExpChar F q] {x : E} : x in perf
ectClosure F E ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E).range
参数：q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_perfectClosure_iff`：mem_perfectClosure_iff {x : E} : x in perfectClo
sure F E ↔ exists n : Nat, x ^ (ringExpChar F) ^ n in (algebraMap F E).range
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_perfectClosure_iff_pow_mem (q : ℕ) [ExpChar F q] {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [mem_perfectClosure_iff, ringExpChar.eq F q]

/-- An element is contained in the relative perfect closure if and only if its minimal polynomial
has separable degree one. -/
/-
**mem_perfectClosure_iff_natSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_perfectClosure_iff_natSepDegree_eq_one {x : E} : x in perfectClosure F
 E ↔ (minpoly F x).natSepDegree = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_perfectClosure_iff`：mem_perfectClosure_iff {x : E} : x in perfectClo
sure F E ↔ exists n : Nat, x ^ (ringExpChar F) ^ n in (algebraMap F E).range
· 使用定理 `minpoly.natSepDegree_eq_one_iff_pow_mem`：natSepDegree_eq_one_iff_pow_mem
 : (minpoly F x).natSepDegree = 1 ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E
).range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is contained in the relative perfect closure if and only if its minim
al polynomial
has separable degree one.
-/
theorem mem_perfectClosure_iff_natSepDegree_eq_one {x : E} :
    x ∈ perfectClosure F E ↔ (minpoly F x).natSepDegree = 1 := by
  rw [mem_perfectClosure_iff, minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]

/-- A field extension `E / F` is purely inseparable if and only if the relative perfect closure of
`F` in `E` is equal to `E`. -/
/-
**isPurelyInseparable_iff_perfectClosure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_perfectClosure_eq_top : IsPurelyInseparable F E ↔ 
perfectClosure F E = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `trivial`：True

--- 原说明 ---
A field extension `E / F` is purely inseparable if and only if the relative perf
ect closure of
`F` in `E` is equal to `E`.
-/
theorem isPurelyInseparable_iff_perfectClosure_eq_top :
    IsPurelyInseparable F E ↔ perfectClosure F E = ⊤ := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H ↦ top_unique fun x _ ↦ H x, fun H _ ↦ H.ge trivial⟩

variable (F E)

/-- The relative perfect closure of `F` in `E` is purely inseparable over `F`. -/
/-
**perfectClosure.isPurelyInseparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure
 F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
The relative perfect closure of `F` in `E` is purely inseparable over `F`.
-/
instance perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure F E) := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ ↦ ⟨n, y, (algebraMap _ E).injective h⟩

/-- The relative perfect closure of `F` in `E` is algebraic over `F`. -/
/-
**perfectClosure.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.isAlgebraic`：IsPurelyInseparable.isAlgebraic [Nontri
vial F] [IsPurelyInseparable F E] : Algebra.IsAlgebraic F E
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
The relative perfect closure of `F` in `E` is algebraic over `F`.
-/
instance perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _

/-- If `E / F` is separable, then the perfect closure of `F` in `E` is equal to `F`. Note that
  the converse is not necessarily true (see https://math.stackexchange.com/a/3009197)
  even when `E / F` is algebraic. -/
/-
**perfectClosure.eq_bot_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectClosure.eq_bot_of_isSeparable [Algebra.IsSeparable F E] : perfectCl
osure F E = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`：Intermed
iateField.eq_bot_of_isPurelyInseparable_of_isSeparable {F : Type u} {E : Type v}
 [Field F] [Field E] [Algebra F E] (L : Intermediate…
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `E / F` is separable, then the perfect closure of `F` in `E` is equal to `F`.
 Note that
  the converse is not necessarily true (see https://math.stackexchange.com/a/300
9197)
  even when `E / F` is algebraic.
-/
theorem perfectClosure.eq_bot_of_isSeparable [Algebra.IsSeparable F E] : perfectClosure F E = ⊥ :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _

/-- An intermediate field of `E / F` is contained in the relative perfect closure of `F` in `E`
if it is purely inseparable over `F`. -/
/-
**le_perfectClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L
] : L <= perfectClosure F E
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field of `E / F` is contained in the relative perfect closure of
 `F` in `E`
if it is purely inseparable over `F`.
-/
theorem le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L] :
    L ≤ perfectClosure F E := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩

/-- An intermediate field of `E / F` is contained in the relative perfect closure of `F` in `E`
if and only if it is purely inseparable over `F`. -/
/-
**le_perfectClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_perfectClosure_iff (L : IntermediateField F E) : L <= perfectClosure F 
E ↔ IsPurelyInseparable F L
参数：L : IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `le_perfectClosure`：le_perfectClosure (L : IntermediateField F E) [h : Is
PurelyInseparable F L] : L <= perfectClosure F E

--- 原说明 ---
An intermediate field of `E / F` is contained in the relative perfect closure of
 `F` in `E`
if and only if it is purely inseparable over `F`.
-/
theorem le_perfectClosure_iff (L : IntermediateField F E) :
    L ≤ perfectClosure F E ↔ IsPurelyInseparable F L := by
  refine ⟨fun h ↦ (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x ↦ ?_,
    fun _ ↦ le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩
/-
**separableClosure_inf_perfectClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosur
e F E = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`：Intermed
iateField.eq_bot_of_isPurelyInseparable_of_isSeparable {F : Type u} {E : Type v}
 [Field F] [Field E] [Algebra F E] (L : Intermediate…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_perfectClosure_iff`：le_perfectClosure_iff (L : IntermediateField F E)
 : L <= perfectClosure F E ↔ IsPurelyInseparable F L
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_separableClosure_iff`：le_separableClosure_iff (L : IntermediateField 
F E) : L <= separableClosure F E ↔ Algebra.IsSeparable F L
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosure F E = ⊥ :=
  haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _

section map

variable {F E K}

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`perfectClosure F K` if and only if `x` is contained in `perfectClosure F E`. -/
/-
**map_mem_perfectClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_perfectClosure_iff (i : E ->ₐ[F] K) {x : E} : i x in perfectClosur
e F K ↔ x in perfectClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained i
n
`perfectClosure F K` if and only if `x` is contained in `perfectClosure F E`.
-/
theorem map_mem_perfectClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ perfectClosure F K ↔ x ∈ perfectClosure F E := by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of `perfectClosure F K`
under the map `i` is equal to `perfectClosure F E`. -/
/-
**perfectClosure.comap_eq_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectClosure.comap_eq_of_algHom (i : E ->ₐ[F] K) : (perfectClosure F K).
comap i = perfectClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `map_mem_perfectClosure_iff`：map_mem_perfectClosure_iff (i : E ->ₐ[F] K) 
{x : E} : i x in perfectClosure F K ↔ x in perfectClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of `per
fectClosure F K`
under the map `i` is equal to `perfectClosure F E`.
-/
theorem perfectClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F K).comap i = perfectClosure F E := by
  ext x
  exact map_mem_perfectClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `perfectClosure F E`
under the map `i` is contained in `perfectClosure F K`. -/
/-
**perfectClosure.map_le_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectClosure.map_le_of_algHom (i : E ->ₐ[F] K) : (perfectClosure F E).ma
p i <= perfectClosure F K
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.map_le_iff_le_comap`：map_le_iff_le_comap {f : L ->ₐ[K]
 L'} {s : IntermediateField K L} {t : IntermediateField K L'} : s.map f <= t ↔ s
 <= t.comap f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `perfectClosure.comap_eq_of_algHom`：perfectClosure.comap_eq_of_algHom (i 
: E ->ₐ[F] K) : (perfectClosure F K).comap i = perfectClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `perfec
tClosure F E`
under the map `i` is contained in `perfectClosure F K`.
-/
theorem perfectClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F E).map i ≤ perfectClosure F K :=
  map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `perfectClosure F E`
under the map `i` is equal to in `perfectClosure F K`. -/
/-
**perfectClosure.map_eq_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) : (perfectClosure F E).m
ap i.toAlgHom = perfectClosure F K
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `perfectClosure.map_le_of_algHom`：perfectClosure.map_le_of_algHom (i : E 
->ₐ[F] K) : (perfectClosure F E).map i <= perfectClosure F K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_mem_perfectClosure_iff`：map_mem_perfectClosure_iff (i : E ->ₐ[F] K) 
{x : E} : i x in perfectClosure F K ↔ x in perfectClosure F E
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `perfectC
losure F E`
under the map `i` is equal to in `perfectClosure F K`.
-/
theorem perfectClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (perfectClosure F E).map i.toAlgHom = perfectClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm (fun x hx ↦ ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `perfectClosure F E` and
`perfectClosure F K` are also isomorphic as `F`-algebras. -/
/-
**perfectClosure.algEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) : perfectClosure F E ≃ₐ[
F] perfectClosure F K
参数：i : E ≃ₐ[F] K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `perfectClosure.map_eq_of_algEquiv`：perfectClosure.map_eq_of_algEquiv (i 
: E ≃ₐ[F] K) : (perfectClosure F E).map i.toAlgHom = perfectClosure F K

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then `perfectClosure F E` and
`perfectClosure F K` are also isomorphic as `F`-algebras.
-/
def perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F E ≃ₐ[F] perfectClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

noncomputable
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

end map

/-- If `E` is a perfect field of exponential characteristic `p`, then the (relative) perfect closure
`perfectClosure F E` is perfect. -/
/-
**perfectClosure.perfectRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：perfectClosure.perfectRing (p : Nat) [ExpChar E p] [PerfectRing E p] : Per
fectRing (perfectClosure F E) p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PerfectRing.ofSurjective`：PerfectRing.ofSurjective (R : Type*) (p : Nat)
 [CommRing R] [ExpChar R p] [IsReduced R] (h : Surjective <| frobenius R p) : Pe
rfectRing R p
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `RingHom.expChar`：RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring 
A] (f : R ->+* A) (H : Function.Injective f) (p : Nat) [ExpChar A p] : ExpChar R
 p
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `surjective_frobenius`：surjective_frobenius : Surjective (frobenius R p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_perfectClosure_iff_pow_mem`：mem_perfectClosure_iff_pow_mem (q : Nat)
 [ExpChar F q] {x : E} : x in perfectClosure F E ↔ exists n : Nat, x ^ q ^ n in 
(algebraMap F E).ran…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `E` is a perfect field of exponential characteristic `p`, then the (relative)
 perfect closure
`perfectClosure F E` is perfect.
-/
instance perfectClosure.perfectRing (p : ℕ) [ExpChar E p]
    [PerfectRing E p] : PerfectRing (perfectClosure F E) p := .ofSurjective _ p fun x ↦ by
  have := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx, ← pow_mul, ← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

/-- If `E` is a perfect field, then the (relative) perfect closure
`perfectClosure F E` is perfect. -/
/-
**perfectClosure.perfectField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：perfectClosure.perfectField [PerfectField E] : PerfectField (perfectClosur
e F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PerfectRing.toPerfectField`：PerfectRing.toPerfectField (K : Type*) (p : 
Nat) [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
If `E` is a perfect field, then the (relative) perfect closure
`perfectClosure F E` is perfect.
-/
instance perfectClosure.perfectField [PerfectField E] : PerfectField (perfectClosure F E) :=
  PerfectRing.toPerfectField _ (ringExpChar E)

end perfectClosure

namespace IntermediateField

/-- `F⟮x⟯ / F` is a purely inseparable extension if and only if the minimal polynomial of `x`
has separable degree one. -/
/-
**IntermediateField.isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one** 
是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one {x : E} : IsPure
lyInseparable F F⟮x⟯ ↔ (minpoly F x).natSepDegree = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_perfectClosure_iff`：le_perfectClosure_iff (L : IntermediateField F E)
 : L <= perfectClosure F E ↔ IsPurelyInseparable F L
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `mem_perfectClosure_iff_natSepDegree_eq_one`：mem_perfectClosure_iff_natSe
pDegree_eq_one {x : E} : x in perfectClosure F E ↔ (minpoly F x).natSepDegree = 
1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`F⟮x⟯ / F` is a purely inseparable extension if and only if the minimal polynomi
al of `x`
has separable degree one.
-/
theorem isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ (minpoly F x).natSepDegree = 1 := by
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_natSepDegree_eq_one]

/-- If `F` is of exponential characteristic `q`, then `F⟮x⟯ / F` is a purely inseparable extension
if and only if `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
/-
**IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem** 是 Mathlib 中的
一个定理，位于命名空间 `IntermediateField`。
形式化陈述：isPurelyInseparable_adjoin_simple_iff_pow_mem (q : Nat) [hF : ExpChar F q]
 {x : E} : IsPurelyInseparable F F⟮x⟯ ↔ exists n : Nat, x ^ q ^ n in (algebraMap
 F E).range
参数：q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_perfectClosure_iff`：le_perfectClosure_iff (L : IntermediateField F E)
 : L <= perfectClosure F E ↔ IsPurelyInseparable F L
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `mem_perfectClosure_iff_pow_mem`：mem_perfectClosure_iff_pow_mem (q : Nat)
 [ExpChar F q] {x : E} : x in perfectClosure F E ↔ exists n : Nat, x ^ q ^ n in 
(algebraMap F E).ran…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `F` is of exponential characteristic `q`, then `F⟮x⟯ / F` is a purely insepar
able extension
if and only if `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.
-/
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_pow_mem q]

/-- If `F` is of exponential characteristic `q`, then `F(S) / F` is a purely inseparable extension
if and only if for any `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
/-
**IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField`。
形式化陈述：isPurelyInseparable_adjoin_iff_pow_mem (q : Nat) [hF : ExpChar F q] {S : S
et E} : IsPurelyInseparable F (adjoin F S) ↔ forall x in S, exists n : Nat, x ^ 
q ^ n in (algebraMap F E).range
参数：q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_perfectClosure_iff_pow_mem`：mem_perfectClosure_iff_pow_mem (q : Nat)
 [ExpChar F q] {x : E} : x in perfectClosure F E ↔ exists n : Nat, x ^ q ^ n in 
(algebraMap F E).ran…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `F` is of exponential characteristic `q`, then `F(S) / F` is a purely insepar
able extension
if and only if for any `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : 
ℕ`.
-/
theorem isPurelyInseparable_adjoin_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {S : Set E} :
    IsPurelyInseparable F (adjoin F S) ↔ ∀ x ∈ S, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]

/-- A compositum of two purely inseparable extensions is purely inseparable. -/
/-
**IntermediateField.isPurelyInseparable_sup** 是 Mathlib 中的一个实例，位于命名空间 `Intermedi
ateField`。
形式化陈述：isPurelyInseparable_sup (L1 L2 : IntermediateField F E) [h1 : IsPurelyInse
parable F L1] [h2 : IsPurelyInseparable F L2] : IsPurelyInseparable F (L1 ⊔ L2 :
 IntermediateField F E)
参数：L1 L2 : IntermediateField F E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_perfectClosure_iff`：le_perfectClosure_iff (L : IntermediateField F E)
 : L <= perfectClosure F E ↔ IsPurelyInseparable F L
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c

--- 原说明 ---
A compositum of two purely inseparable extensions is purely inseparable.
-/
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of purely inseparable extensions is purely inseparable. -/
/-
**IntermediateField.isPurelyInseparable_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Intermed
iateField`。
形式化陈述：isPurelyInseparable_iSup {ι : Sort*} {t : ι -> IntermediateField F E} [h :
 forall i, IsPurelyInseparable F (t i)] : IsPurelyInseparable F (⨆ i, t i : Inte
rmediateField F E)
参数：t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
A compositum of purely inseparable extensions is purely inseparable.
-/
instance isPurelyInseparable_iSup {ι : Sort*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ (q ^ n))` for any natural number `n`. -/
/-
**IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable** 是 Mathlib 
中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [Algebra.IsSep
arable F (adjoin F S)] (q : Nat) [ExpChar F q] (n : Nat) : adjoin F S = adjoin F
 ((· ^ q ^ n) '' S)
参数：S : Set E；adjoin F S；q : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.isSeparable_adjoin_iff_isSeparable`：IntermediateField.
isSeparable_adjoin_iff_isSeparable {S : Set E} : Algebra.IsSeparable F (adjoin F
 S) ↔ forall x in S, IsSeparable F x
· 使用定理 `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem`：isPurel
yInseparable_adjoin_simple_iff_pow_mem (q : Nat) [hF : ExpChar F q] {x : E} : Is
PurelyInseparable F F⟮x⟯ ↔ exists n : Nat, x ^ q ^ n …
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`：Intermed
iateField.eq_bot_of_isPurelyInseparable_of_isSeparable {F : Type u} {E : Type v}
 [Field F] [Field E] [Algebra F E] (L : Intermediate…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …

--- 原说明 ---
If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, th
en
`F(S) = F(S ^ (q ^ n))` for any natural number `n`.
-/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E)
    [Algebra.IsSeparable F (adjoin F S)] (q : ℕ) [ExpChar F q] (n : ℕ) :
    adjoin F S = adjoin F ((· ^ q ^ n) '' S) := by
  set M := adjoin F ((· ^ q ^ n) '' S)
  have := expChar_of_injective_algebraMap (algebraMap F M).injective q
  refine le_antisymm (adjoin_le_iff.2 fun x hx ↦ ?_) (adjoin_le_iff.2 ?_)
  · have : Algebra.IsSeparable M M⟮x⟯ :=
      (isSeparable_adjoin_simple_iff_isSeparable M E).2 <|
        ((isSeparable_adjoin_iff_isSeparable F E).1 inferInstance x hx).tower_top M
    have : IsPurelyInseparable M M⟮x⟯ :=
      (isPurelyInseparable_adjoin_simple_iff_pow_mem M E q).2
        ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
    have hx' := mem_adjoin_simple_self M x
    rw [M⟮x⟯.eq_bot_of_isPurelyInseparable_of_isSeparable, mem_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ (q ^ n))` for any subset `S` of `E` and any natural number `n`. -/
/-
**IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'** 是 Mathlib
 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E]
 (S : Set E) (q : Nat) [ExpChar F q] (n : Nat) : adjoin F S = adjoin F ((· ^ q ^
 n) '' S)
参数：S : Set E；q : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable`：adjoi
n_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [Algebra.IsSeparable F (a
djoin F S)] (q : Nat) [ExpChar F q] (n : Nat) : adjoin …
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `E / F` is a separable field extension of exponential characteristic `q`, the
n
`F(S) = F(S ^ (q ^ n))` for any subset `S` of `E` and any natural number `n`.
-/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

-- TODO: prove the converse when `F(S) / F` is finite
/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ q)`. -/
/-
**IntermediateField.adjoin_eq_adjoin_pow_expChar_of_isSeparable** 是 Mathlib 中的一个
定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [Algebra.IsSeparab
le F (adjoin F S)] (q : Nat) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S
)
参数：S : Set E；adjoin F S；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable`：adjoi
n_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [Algebra.IsSeparable F (a
djoin F S)] (q : Nat) [ExpChar F q] (n : Nat) : adjoin …
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, th
en
`F(S) = F(S ^ q)`.
-/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [Algebra.IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ q)` for any subset `S` of `E`. -/
/-
**IntermediateField.adjoin_eq_adjoin_pow_expChar_of_isSeparable'** 是 Mathlib 中的一
个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (S 
: Set E) (q : Nat) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S)
参数：S : Set E；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'`：adjo
in_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set 
E) (q : Nat) [ExpChar F q] (n : Nat) : adjoin F S = adjo…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `E / F` is a separable field extension of exponential characteristic `q`, the
n
`F(S) = F(S ^ q)` for any subset `S` of `E`.
-/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

-- Special cases for simple adjoin

/-- If `F` is a field of exponential characteristic `q`, `a : E` is separable over `F`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any natural number `n`. -/
/-
**IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable** 是 M
athlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSep
arable F a) (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n⟯
参数：ha : IsSeparable F a；q : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable`：adjoi
n_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [Algebra.IsSeparable F (a
djoin F S)] (q : Nat) [ExpChar F q] (n : Nat) : adjoin …

--- 原说明 ---
If `F` is a field of exponential characteristic `q`, `a : E` is separable over `
F`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any natural number `n`.
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : ℕ) [ExpChar F q] (n : ℕ) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  have := (isSeparable_adjoin_simple_iff_isSeparable F E).mpr ha
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any subset `a : E` and any natural number `n`. -/
/-
**IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable'** 是 
Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparab
le F E] (a : E) (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n⟯
参数：a : E；q : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable`：adjoi
n_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [Algebra.IsSeparable F (a
djoin F S)] (q : Nat) [ExpChar F q] (n : Nat) : adjoin …

--- 原说明 ---
If `E / F` is a separable field extension of exponential characteristic `q`, the
n
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any subset `a : E` and any natural number `n`.
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/-- If `F` is a field of exponential characteristic `q`, `a : E` is separable over `F`, then
`F⟮a⟯ = F⟮a ^ q⟯`. -/
/-
**IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable** 是 Mathl
ib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable {a : E} (ha : IsSeparab
le F a) (q : Nat) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯
参数：ha : IsSeparable F a；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
`：adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSeparab
le F a) (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `F` is a field of exponential characteristic `q`, `a : E` is separable over `
F`, then
`F⟮a⟯ = F⟮a ^ q⟯`.
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : ℕ) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E ha q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F⟮a⟯ = F⟮a ^ q⟯` for any `a : E`. -/
/-
**IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'** 是 Math
lib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F
 E] (a : E) (q : Nat) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯
参数：a : E；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
'`：adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable 
F E] (a : E) (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `E / F` is a separable field extension of exponential characteristic `q`, the
n
`F⟮a⟯ = F⟮a ^ q⟯` for any `a : E`.
-/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : ℕ) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a q 1

end IntermediateField

section

variable (q n : ℕ) [hF : ExpChar F q] {ι : Type*} {v : ι → E} {F E}

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a family
of elements of `E` which `F`-linearly spans `E`, then `{ u_i ^ (q ^ n) }` also `F`-linearly spans
`E` for any natural number `n`. -/
/-
**Field.span_map_pow_expChar_pow_eq_top_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [Algebra.IsSeparable 
F E] (h : Submodule.span F (Set.range v) = ⊤) : Submodule.span F (Set.range (v ·
 ^ q ^ n)) = ⊤
参数：h : Submodule.span F (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
· 使用定理 `IntermediateField.top_toSubalgebra`：top_toSubalgebra : (⊤ : Intermediate
Field F E).toSubalgebra = ⊤
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤
· 使用定理 `IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable'`：adjo
in_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set 
E) (q : Nat) [ExpChar F q] (n : Nat) : adjoin F S = adjo…
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Submodule.image_span_subset_span`：image_span_subset_span (f : M ->ₛₗ[σ₁₂
] M₂) (s : Set M) : f '' span R s subseteq span R₂ (f '' s)

--- 原说明 ---
If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i
 }` is a family
of elements of `E` which `F`-linearly spans `E`, then `{ u_i ^ (q ^ n) }` also `
F`-linearly spans
`E` for any natural number `n`.
-/
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [Algebra.IsSeparable F E]
    (h : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span F (Set.range (v · ^ q ^ n)) = ⊤ := by
  rw [← Algebra.top_toSubmodule, ← top_toSubalgebra, ← adjoin_univ,
    adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n,
    adjoin_toSubalgebra_of_isAlgebraic fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x,
    Set.image_univ, Algebra.adjoin_eq_span]
  have := (MonoidHom.mrange (powMonoidHom (α := E) (q ^ n))).closure_eq
  simp only [MonoidHom.mrange, powMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_copy] at this
  rw [this]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp, ← Set.image_univ]
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _

/-- If `E / F` is a finite separable extension of exponential characteristic `q`, if `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }` is also
`F`-linearly independent for any natural number `n`. A special case of
`LinearIndependent.map_pow_expChar_pow_of_isSeparable`
and is an intermediate result used to prove it. -/
/-
**LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable** 是 Mathlib 中的一个定理，位于命
名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E / F` is a finite separable extension of exponential characteristic `q`, if
 `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ 
n) }` is also
`F`-linearly independent for any natural number `n`. A special case of
`LinearIndependent.map_pow_expChar_pow_of_isSeparable`
and is an intermediate result used to prove it.
-/
private theorem LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have h' := h.linearIndepOn_id
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  let : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (Module.finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert! H.comp f fun _ _ heq ↦ h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }` is also
`F`-linearly independent for any natural number `n`. -/
/-
**LinearIndependent.map_pow_expChar_pow_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：LinearIndependent.map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable 
F E] (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n)
参数：h : LinearIndependent F v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff_finset_linearIndependent`：linearIndependent_iff_fi
nset_linearIndependent : LinearIndependent R v ↔ forall (s : Finset ι), LinearIn
dependent R (v ∘ (Subtype.val : s ->…
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `_private.Mathlib.FieldTheory.PurelyInseparable.PerfectClosure.0.LinearIn
dependent.map_pow_expChar_pow_of_fd_isSeparable`：∀ {F : Type u} {E : Type v} [in
st : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (q n : ℕ) [hF : ExpChar 
F q]   {ι : Type u_1} {v : ι …
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A

--- 原说明 ---
If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i
 }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ 
n) }` is also
`F`-linearly independent for any natural number `n`.
-/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  have : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a field extension of exponential characteristic `q`, if `{ u_i }` is a
family of separable elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }`
is also `F`-linearly independent for any natural number `n`. -/
/-
**LinearIndependent.map_pow_expChar_pow_of_isSeparable'** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：LinearIndependent.map_pow_expChar_pow_of_isSeparable' (hsep : forall i : ι
, IsSeparable F (v i)) (h : LinearIndependent F v) : LinearIndependent F (v · ^ 
q ^ n)
参数：hsep : forall i : ι, IsSeparable F (v i)；h : LinearIndependent F v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_iff_isSeparable`：IntermediateField.
isSeparable_adjoin_iff_isSeparable {S : Set E} : Algebra.IsSeparable F (adjoin F
 S) ↔ forall x in S, IsSeparable F x
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `LinearIndependent.map_pow_expChar_pow_of_isSeparable`：LinearIndependent.
map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable F E] (h : LinearIndepend
ent F v) : LinearIndependent F (v · ^ q ^ …
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `E / F` is a field extension of exponential characteristic `q`, if `{ u_i }` 
is a
family of separable elements of `E` which is `F`-linearly independent, then `{ u
_i ^ (q ^ n) }`
is also `F`-linearly independent for any natural number `n`.
-/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable'
    (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  let E' := adjoin F (Set.range v)
  have : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 <| by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is an
`F`-basis of `E`, then `{ u_i ^ (q ^ n) }` is also an `F`-basis of `E`
for any natural number `n`. -/
/-
**Module.Basis.mapPowExpCharPowOfIsSeparable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Basis.mapPowExpCharPowOfIsSeparable [Algebra.IsSeparable F E] (b : 
Basis ι F E) : Basis ι F E
参数：b : Basis ι F E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i
 }` is an
`F`-basis of `E`, then `{ u_i ^ (q ^ n) }` is also an `F`-basis of `E`
for any natural number `n`.
-/
def Module.Basis.mapPowExpCharPowOfIsSeparable [Algebra.IsSeparable F E] (b : Basis ι F E) :
    Basis ι F E :=
  .mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

/-- For an extension `E / F` of exponential characteristic `q` and a separable element `a : E`, the
minimal polynomial of `a ^ q ^ n` equals the minimal polynomial of `a` mapped via `(⬝ ^ q ^ n)`. -/
/-
**minpoly.iterateFrobenius_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minpoly.iterateFrobenius_of_isSeparable [ExpChar E q] (n : Nat) {a : E} (h
sep : IsSeparable F a) : minpoly F (iterateFrobenius E q n a) = (minpoly F a).ma
p (iterateFrobenius F q n)
参数：n : Nat；hsep : IsSeparable F a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用引理 `RingHom.iterateFrobenius_comm`：RingHom.iterateFrobenius_comm (n : Nat) :
 g.comp (iterateFrobenius R p n) = (iterateFrobenius S p n).comp g
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable
`：adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSeparab
le F a) (q : Nat) [ExpChar F q] (n : Nat) : F⟮a⟯ = F⟮a ^ q ^ n…
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For an extension `E / F` of exponential characteristic `q` and a separable eleme
nt `a : E`, the
minimal polynomial of `a ^ q ^ n` equals the minimal polynomial of `a` mapped vi
a `(⬝ ^ q ^ n)`.
-/
theorem minpoly.iterateFrobenius_of_isSeparable [ExpChar E q] (n : ℕ) {a : E}
    (hsep : IsSeparable F a) :
    minpoly F (iterateFrobenius E q n a) = (minpoly F a).map (iterateFrobenius F q n) := by
  have hai : IsIntegral F a := hsep.isIntegral
  have hapi : IsIntegral F (iterateFrobenius E q n a) := hai.pow _
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hapi)
    (minpoly.monic hai |>.map _)
    (minpoly.dvd F (a ^ q ^ n) ?haeval)
    ?hdeg
  · simpa using! Eq.symm <|
      (minpoly F a).map_aeval_eq_aeval_map (RingHom.iterateFrobenius_comm _ q n) a
  · rw [(minpoly F a).natDegree_map_eq_of_injective (iterateFrobenius F q n).injective,
      ← IntermediateField.adjoin.finrank hai,
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep q n,
      ← IntermediateField.adjoin.finrank hapi, iterateFrobenius_def]

/-- For an extension `E / F` of exponential characteristic `q` and a separable element `a : E`, the
minimal polynomial of `a ^ q` equals the minimal polynomial of `a` mapped via `(⬝ ^ q)`. -/
/-
**minpoly.frobenius_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minpoly.frobenius_of_isSeparable [ExpChar E q] {a : E} (hsep : IsSeparable
 F a) : minpoly F (frobenius E q a) = (minpoly F a).map (frobenius F q)
参数：hsep : IsSeparable F a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
· 使用定理 `minpoly.iterateFrobenius_of_isSeparable`：minpoly.iterateFrobenius_of_isS
eparable [ExpChar E q] (n : Nat) {a : E} (hsep : IsSeparable F a) : minpoly F (i
terateFrobenius E q n a) = (m…

--- 原说明 ---
For an extension `E / F` of exponential characteristic `q` and a separable eleme
nt `a : E`, the
minimal polynomial of `a ^ q` equals the minimal polynomial of `a` mapped via `(
⬝ ^ q)`.
-/
theorem minpoly.frobenius_of_isSeparable [ExpChar E q] {a : E} (hsep : IsSeparable F a) :
    minpoly F (frobenius E q a) = (minpoly F a).map (frobenius F q) := by
  simpa using minpoly.iterateFrobenius_of_isSeparable q 1 hsep

end

/-
**perfectField_of_perfectClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectCl
osure F E = ⊥) : PerfectField F
参数：eq : perfectClosure F E = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `PerfectRing.ofSurjective`：PerfectRing.ofSurjective (R : Type*) (p : Nat)
 [CommRing R] [ExpChar R p] [IsReduced R] (h : Surjective <| frobenius R p) : Pe
rfectRing R p
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `surjective_frobenius`：surjective_frobenius : Surjective (frobenius R p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
· 使用引理 `RingHom.map_frobenius`：RingHom.map_frobenius : g (frobenius R p x) = fro
benius S p (g x)
· 使用引理 `PerfectRing.toPerfectField`：PerfectRing.toPerfectField (K : Type*) (p : 
Nat) [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K
-/
theorem perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) :
    PerfectField F := by
  let p := ringExpChar F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y ∈ perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    simp only [Algebra.ofId] at h
    exact ⟨z, (algebraMap F E).injective (by rw [RingHom.map_frobenius]; rw [h])⟩
  exact PerfectRing.toPerfectField F p

/-- If `E / F` is a separable extension, `E` is perfect, then `F` is also perfect. -/
/-
**perfectField_of_isSeparable_of_perfectField_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectField_of_isSeparable_of_perfectField_top [Algebra.IsSeparable F E] 
[PerfectField E] : PerfectField F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `perfectField_of_perfectClosure_eq_bot`：perfectField_of_perfectClosure_eq
_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) : PerfectField F
· 使用定理 `perfectClosure.eq_bot_of_isSeparable`：perfectClosure.eq_bot_of_isSeparab
le [Algebra.IsSeparable F E] : perfectClosure F E = ⊥

--- 原说明 ---
If `E / F` is a separable extension, `E` is perfect, then `F` is also perfect.
-/
theorem perfectField_of_isSeparable_of_perfectField_top [Algebra.IsSeparable F E] [PerfectField E] :
    PerfectField F :=
  perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

/-- If `E` is an algebraic closure of `F`, then `F` is perfect if and only if `E / F` is
separable. -/
/-
**perfectField_iff_isSeparable_algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] : Perfect
Field F ↔ Algebra.IsSeparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSepClosure.separable`：∀ {k : Type u} {inst : Field k} {K : Type v} {in
st_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   Algebra.IsSe
parable k K
· 使用定理 `IsSepClosure.of_isAlgClosure_of_perfectField`：∀ (k : Type u) [inst : Fie
ld k] (K : Type v) [inst_1 : Field K] [inst_2 : Algebra k K] [IsAlgClosure k K] 
  [PerfectField k], IsSepClosure k…
· 使用定理 `perfectField_of_isSeparable_of_perfectField_top`：perfectField_of_isSepar
able_of_perfectField_top [Algebra.IsSeparable F E] [PerfectField E] : PerfectFie
ld F
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k
· 使用定理 `IsAlgClosure.isAlgClosed`：∀ (R : Type u) {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…

--- 原说明 ---
If `E` is an algebraic closure of `F`, then `F` is perfect if and only if `E / F
` is
separable.
-/
theorem perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] :
    PerfectField F ↔ Algebra.IsSeparable F E :=
  ⟨fun _ ↦ IsSepClosure.separable, fun _ ↦ haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩
