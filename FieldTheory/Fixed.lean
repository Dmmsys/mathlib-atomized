/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `FixedPoints.subfield G F`,
the subfield consisting of elements of `F` fixed by every element of `G`.

This subfield is then normal and separable, and in addition if `G` acts faithfully on `F`
then `finrank (FixedPoints.subfield G F) F = Fintype.card G`.

## Main Definitions

- `FixedPoints.subfield G F`, the subfield consisting of elements of `F` fixed by every
  element of `G`, where `G` is a group that acts on `F`.
-/

@[expose] public section


noncomputable section

open MulAction Finset Module

universe u v w

variable {M : Type u} [Monoid M]
variable (G : Type u) [Group G]
variable (K : Type*) (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/-- The subfield of `F` fixed by the field endomorphism `m`. -/
/-
**FixedBy.subfield** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedBy.subfield : Subfield F where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfield of `F` fixed by the field endomorphism `m`.
-/
def FixedBy.subfield : Subfield F where
  carrier := fixedBy F m
  zero_mem' := smul_zero m
  add_mem' hx hy := (smul_add m _ _).trans <| congr_arg₂ _ hx hy
  neg_mem' hx := (smul_neg m _).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' hx hy := (smul_mul' m _ _).trans <| congr_arg₂ _ hx hy
  inv_mem' x hx := (smul_inv'' m x).trans <| congr_arg _ hx

@[simp]
/-
**FixedBy.subfield_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FixedBy.subfield_mem_iff (x : F) : x in FixedBy.subfield F m ↔ m • x = x
参数：x : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem FixedBy.subfield_mem_iff (x : F) :
    x ∈ FixedBy.subfield F m ↔ m • x = x := Iff.rfl

variable [Field K] [Algebra K F] [SMulCommClass M K F]

/-- The intermediate field between `K` and `F` fixed by the field endomorphism `m`. -/
/-
**FixedBy.intermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedBy.intermediateField : IntermediateField K F where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate field between `K` and `F` fixed by the field endomorphism `m`.
-/
def FixedBy.intermediateField : IntermediateField K F where
  __ := FixedBy.subfield F m
  algebraMap_mem' x := smul_algebraMap m x

@[simp]
/-
**FixedBy.intermediateField_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FixedBy.intermediateField_mem_iff (x : F) : x in FixedBy.intermediateField
 K F m ↔ m • x = x
参数：x : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem FixedBy.intermediateField_mem_iff (x : F) :
    x ∈ FixedBy.intermediateField K F m ↔ m • x = x := Iff.rfl

section InvariantSubfields

variable (M) {F}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
/-
**IsInvariantSubfield** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u) → [inst : Monoid M] → {F : Type v} → [inst_1 : Field F] → [Mu
lSemiringAction M F] → Subfield F → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for subrings invariant under a `MulSemiringAction`.
-/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : ∀ (m : M) {x : F}, x ∈ S → m • x ∈ S

variable (S : Subfield F)
/-
**IsInvariantSubfield.toMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsInvariantSubfield.toMulSemiringAction [IsInvariantSubfield M S] : MulSem
iringAction M S where smul m x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsInvariantSubfield.toMulSemiringAction [IsInvariantSubfield M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • x.1, IsInvariantSubfield.smul_mem m x.2⟩
  one_smul s := Subtype.ext <| one_smul M s.1
  mul_smul m₁ m₂ s := Subtype.ext <| mul_smul m₁ m₂ s.1
  smul_add m s₁ s₂ := Subtype.ext <| smul_add m s₁.1 s₂.1
  smul_zero m := Subtype.ext <| smul_zero m
  smul_one m := Subtype.ext <| smul_one m
  smul_mul m s₁ s₂ := Subtype.ext <| smul_mul' m s₁.1 s₂.1
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsInvariantSubfield M S] : IsInvariantSubring M S.toSubring where
  smul_mem := IsInvariantSubfield.smul_mem

end InvariantSubfields

namespace FixedPoints

variable (M)

set_option backward.isDefEq.respectTransparency.types false in
-- we use `Subfield.copy` so that the underlying set is `fixedPoints M F`
/-- The subfield of fixed points by a monoid action. -/
/-
**FixedPoints.subfield** 是 Mathlib 中的一个定义，位于命名空间 `FixedPoints`。
形式化陈述：subfield : Subfield F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfield of fixed points by a monoid action.
-/
def subfield : Subfield F :=
  Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext; simp [FixedBy.subfield])
/-
**FixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsInvariantSubfield M (FixedPoints.subfield M F) where
  smul_mem g x hx g' := by rw [hx, hx]
/-
**FixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass M (FixedPoints.subfield M F) F where
  smul_comm m f f' := show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]
/-
**FixedPoints.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
形式化陈述：smulCommClass' : SMulCommClass (FixedPoints.subfield M F) M F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
-/
instance smulCommClass' : SMulCommClass (FixedPoints.subfield M F) M F :=
  SMulCommClass.symm _ _ _

@[simp]
/-
**FixedPoints.smul** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：smul (m : M) (x : FixedPoints.subfield M F) : m • x = x
参数：m : M；x : FixedPoints.subfield M F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `FixedPoints.instIsInvariantSubfieldSubfield`：∀ (M : Type u) [inst : Mono
id M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M F],   IsInva
riantSubfield M (FixedPoints.subf…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
  Subtype.ext <| x.2 m

-- Why is this so slow?
@[simp]
/-
**FixedPoints.smul_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • 
p = p
参数：m : M；p : Polynomial (FixedPoints.subfield M F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `FixedPoints.instIsInvariantSubfieldSubfield`：∀ (M : Type u) [inst : Mono
id M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M F],   IsInva
riantSubfield M (FixedPoints.subf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
· 使用定理 `FixedPoints.smul`：smul (m : M) (x : FixedPoints.subfield M F) : m • x = 
x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用定理 `smul_pow'`：∀ {M : Type u_2} {A : Type u_3} [inst : Monoid M] [inst_1 : M
onoid A] [inst_2 : MulDistribMulAction M A] (r : M) (x : A)   (n : ℕ), r • x ^ …
· 使用定理 `Polynomial.smul_X`：smul_X (m : M) : (m • X : R[X]) = X
-/
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
    rw [smul_mul', Polynomial.smul_C, smul, smul_pow', Polynomial.smul_X]
/-
**FixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (FixedPoints.subfield M F) F := by infer_instance
/-
**FixedPoints.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：coe_algebraMap : algebraMap (FixedPoints.subfield M F) F = Subfield.subtyp
e (FixedPoints.subfield M F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem coe_algebraMap :
    algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl
/-
**FixedPoints.linearIndependent_smul_of_linearIndependent** 是 Mathlib 中的一个定理，位于命
名空间 `FixedPoints`。
形式化陈述：linearIndependent_smul_of_linearIndependent {s : Finset F} : (LinearIndepO
n (FixedPoints.subfield G F) id (s : Set F)) -> LinearIndepOn F (MulAction.toFun
 G F) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `linearIndepOn_insert`：linearIndepOn_insert {s : Set ι} {a : ι} {f : ι ->
 V} (has : a ∉ s) : LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉
 Submodule…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `MulAction.toFun_apply`：toFun_apply (x : M) (y : α) : MulAction.toFun M α
 y x = x • y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
（共 45 条，此处仅展示前 30 条）
-/
theorem linearIndependent_smul_of_linearIndependent {s : Finset F} :
    (LinearIndepOn (FixedPoints.subfield G F) id (s : Set F)) →
      LinearIndepOn F (MulAction.toFun G F) s := by
  classical
  have : IsEmpty ((∅ : Finset F) : Set F) := by simp
  refine Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => ?_
  rw [coe_insert] at hs ⊢
  rw [linearIndepOn_insert (mt mem_coe.1 has)] at hs
  rw [linearIndepOn_insert (mt mem_coe.1 has)]; refine ⟨ih hs.1, fun ha => ?_⟩
  rw [Finsupp.mem_span_image_iff_linearCombination] at ha; rcases ha with ⟨l, hl, hla⟩
  rw [Finsupp.linearCombination_apply_of_mem_supported F hl] at hla
  suffices ∀ i ∈ s, l i ∈ FixedPoints.subfield G F by
    replace hla := (sum_apply _ _ fun i => l i • toFun G F i).symm.trans (congr_fun hla 1)
    simp_rw [Pi.smul_apply, toFun_apply, one_smul] at hla
    refine hs.2 (hla ▸ Submodule.sum_mem _ fun c hcs => ?_)
    change (⟨l c, this c hcs⟩ : FixedPoints.subfield G F) • c ∈ _
    exact Submodule.smul_mem _ _ <| Submodule.subset_span <| by simpa
  intro i his g
  refine
    eq_of_sub_eq_zero
      (linearIndependent_iff'.1 (ih hs.1) s.attach (fun i => g • l i - l i) ?_ ⟨i, his⟩
          (mem_attach _ _) :
        _)
  refine (sum_attach s fun i ↦ (g • l i - l i) • MulAction.toFun G F i).trans ?_
  ext g'
  conv_lhs =>
    rw [Finset.sum_apply]
    congr
    · skip
    · ext
      rw [Pi.smul_apply, sub_smul, smul_eq_mul]
  rw [sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  conv_lhs =>
    congr
    · skip
    · ext x
      rw [toFun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← toFun_apply _ x]
  change
    (∑ x ∈ s, g • (fun y => l y • MulAction.toFun G F y) x (g⁻¹ * g')) =
      ∑ x ∈ s, (fun y => l y • MulAction.toFun G F y) x g'
  rw [← smul_sum, ← sum_apply _ _ fun y => l y • toFun G F y, ←
    sum_apply _ _ fun y => l y • toFun G F y]
  rw [hla, toFun_apply, toFun_apply, smul_smul, mul_inv_cancel_left]

section Fintype

variable [Fintype G] (x : F)

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `FixedPoints.subfield G F`. -/
/-
**FixedPoints.minpoly** 是 Mathlib 中的一个定义，位于命名空间 `FixedPoints`。
形式化陈述：minpoly : Polynomial (FixedPoints.subfield G F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`minpoly G F x` is the minimal polynomial of `(x : F)` over `FixedPoints.subfiel
d G F`.
-/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n

namespace minpoly

set_option backward.isDefEq.respectTransparency.types false in
/-
**FixedPoints.minpoly.monic** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly`。
形式化陈述：monic : (minpoly G F x).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monic_toSubring`：monic_toSubring : Monic (toSubring p T hp) ↔
 Monic p
· 使用定理 `prodXSubSMul.monic`：prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Mo
nic
-/
theorem monic : (minpoly G F x).Monic := by
  simp only [minpoly]
  rw [Polynomial.monic_toSubring]
  exact prodXSubSMul.monic G F x

set_option backward.isDefEq.respectTransparency.types false in
/-
**FixedPoints.minpoly.eval** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂ :
    Polynomial.eval₂ (Subring.subtype <| (FixedPoints.subfield G F).toSubring) x (minpoly G F x) =
      0 := by
  rw [← prodXSubSMul.eval G F x, Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_toSubring]
/-
**FixedPoints.minpoly.eval** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂' :
    Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x
/-
**FixedPoints.minpoly.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly`。
形式化陈述：ne_one : minpoly G F x != (1 : Polynomial (FixedPoints.subfield G F))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `FixedPoints.minpoly.eval₂`：eval₂ : Polynomial.eval₂ (Subring.subtype <| 
(FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_one`：eval₂_one : (1 : R[X]).eval₂ f x = 1
-/
theorem ne_one : minpoly G F x ≠ (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
  (one_ne_zero : (1 : F) ≠ 0) <| by rwa [H, Polynomial.eval₂_one] at this

set_option backward.isDefEq.respectTransparency.types false in
/-
**FixedPoints.minpoly.of_eval** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x f = 0) :
    minpoly G F x ∣ f := by
  classical
  rw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F), minpoly,
    ← Subfield.toSubring_subtype_eq_subtype, Polynomial.map_toSubring _ _, prodXSubSMul]
  refine
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulAction.injective_ofQuotientStabilizer G x) fun y =>
      QuotientGroup.induction_on y fun g => ?_
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, MulAction.ofQuotientStabilizer_mk,
    Polynomial.eval_smul',
    ← IsInvariantSubring.coe_subtypeHom' G (FixedPoints.subfield G F).toSubring,
    ← MulSemiringActionHom.coe_polynomial, ← map_smul, smul_polynomial,
    MulSemiringActionHom.coe_polynomial, IsInvariantSubring.coe_subtypeHom',
    Polynomial.eval_map, Subfield.toSubring_subtype_eq_subtype, hf, smul_zero]

-- Why is this so slow?
/-
**FixedPoints.minpoly.irreducible_aux** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.min
poly`。
形式化陈述：irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Moni
c) (hg : g.Monic) (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1
参数：f g : Polynomial (FixedPoints.subfield G F)；hf : f.Monic；hg : g.Monic；hfg : f
 * g = minpoly G F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `FixedPoints.minpoly.eval₂`：eval₂ : Polynomial.eval₂ (Subring.subtype <| 
(FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `FixedPoints.minpoly.monic`：monic : (minpoly G F x).Monic
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddMemClass.isCancelAdd`：∀ {M : Type u_1} {A : Type u_3} [inst : Add M] 
[inst_1 : SetLike A M] [hA : AddMemClass A M] [IsCancelAdd M] (S : A),   IsCance
lAdd ↥S
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `FixedPoints.minpoly.of_eval₂`：of_eval₂ (f : Polynomial (FixedPoints.subf
ield G F)) (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F)
 x f = 0) : minpol…
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
（共 33 条，此处仅展示前 30 条）
-/
theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg, Polynomial.eval₂_mul, mul_eq_zero] at this
  rcases this with this | this
  · right
    have hf3 : f = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 <| @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_one (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
  · left
    have hg3 : g = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 <| @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mul (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg
/-
**FixedPoints.minpoly.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints.minpoly
`。
形式化陈述：irreducible : Irreducible (minpoly G F x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用引理 `Polynomial.irreducible_of_monic`：irreducible_of_monic (hp : p.Monic) (hp
1 : p != 1) : Irreducible p ↔ forall f g : R[X], f.Monic -> g.Monic -> f * g = p
 -> f = 1 ∨ g = 1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `FixedPoints.minpoly.monic`：monic : (minpoly G F x).Monic
· 使用定理 `FixedPoints.minpoly.ne_one`：ne_one : minpoly G F x != (1 : Polynomial (F
ixedPoints.subfield G F))
· 使用定理 `FixedPoints.minpoly.irreducible_aux`：irreducible_aux (f g : Polynomial (
FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic) (hfg : f * g = minpoly 
G F x) : f = 1 ∨ g = 1
-/
theorem irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

end Fintype

/-
**FixedPoints.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：isIntegral [Finite G] (x : F) : IsIntegral (FixedPoints.subfield G F) x
参数：x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `FixedPoints.minpoly.monic`：monic : (minpoly G F x).Monic
· 使用定理 `FixedPoints.minpoly.eval₂`：eval₂ : Polynomial.eval₂ (Subring.subtype <| 
(FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0
-/
theorem isIntegral [Finite G] (x : F) : IsIntegral (FixedPoints.subfield G F) x := by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

section Fintype

variable [Fintype G] (x : F)

/-
**FixedPoints.minpoly_eq_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield 
G F) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FixedPoints.minpoly.irreducible`：irreducible : Irreducible (minpoly G F 
x)
· 使用定理 `FixedPoints.minpoly.eval₂`：eval₂ : Polynomial.eval₂ (Subring.subtype <| 
(FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0
· 使用定理 `FixedPoints.minpoly.monic`：monic : (minpoly G F x).Monic
-/
theorem minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)
/-
**FixedPoints.rank_le_card** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：rank_le_card : Module.rank (FixedPoints.subfield G F) F <= Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_le`：rank_le {n : Nat} (H : forall s : Finset M, (LinearIndependent 
R fun i : s => (i : M)) -> s.card <= n) : Module.rank R M <= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_coe_finset`：mk_coe_finset {α : Type u} {s : Finset α} : #s =
 ↑(Finset.card s)
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `rank_fun'`：rank_fun' : Module.rank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `FixedPoints.linearIndependent_smul_of_linearIndependent`：linearIndepende
nt_smul_of_linearIndependent {s : Finset F} : (LinearIndepOn (FixedPoints.subfie
ld G F) id (s : Set F)) -> LinearIndepOn F (M…
-/
theorem rank_le_card : Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G :=
  rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Nat.cast_le] using
      (linearIndependent_smul_of_linearIndependent G F hs).cardinal_lift_le_rank

end Fintype

section Finite

variable [Finite G]

set_option backward.isDefEq.respectTransparency.types false in
/-
**FixedPoints.normal** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
形式化陈述：normal : Normal (FixedPoints.subfield G F) F where isAlgebraic x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FixedPoints.isIntegral`：isIntegral [Finite G] (x : F) : IsIntegral (Fixe
dPoints.subfield G F) x
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FixedPoints.minpoly_eq_minpoly`：minpoly_eq_minpoly : minpoly G F x = _ro
ot_.minpoly (FixedPoints.subfield G F) x
· 使用定理 `FixedPoints.minpoly.eq_1`：∀ (G : Type u) [inst : Group G] (F : Type v) [
inst_1 : Field F] [inst_2 : MulSemiringAction G F] [inst_3 : Fintype G]   (x : F
), FixedPoints…
· 使用定理 `FixedPoints.coe_algebraMap`：coe_algebraMap : algebraMap (FixedPoints.sub
field M F) F = Subfield.subtype (FixedPoints.subfield M F)
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subfield.toSubring_subtype_eq_subtype`：toSubring_subtype_eq_subtype (S :
 Subfield K) : S.toSubring.subtype = S.subtype
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用定理 `prodXSubSMul.eq_1`：∀ (G : Type u_2) [inst : Group G] [inst_1 : Fintype G
] (R : Type u_3) [inst_2 : CommRing R]   [inst_3 : MulSemiringAction G R] (x : R
),   pr…
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
-/
instance normal : Normal (FixedPoints.subfield G F) F where
  isAlgebraic x := (isIntegral G F x).isAlgebraic
  splits' x := by
    cases nonempty_fintype G
    rw [← minpoly_eq_minpoly, minpoly, coe_algebraMap, ← Subfield.toSubring_subtype_eq_subtype,
      Polynomial.map_toSubring _ (subfield G F).toSubring, prodXSubSMul]
    exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _

set_option backward.isDefEq.respectTransparency.types false in
/-
**FixedPoints.isSeparable** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
形式化陈述：isSeparable : Algebra.IsSeparable (FixedPoints.subfield G F) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSeparable.eq_1`：∀ (F : Type u_1) {K : Type u_3} [inst : CommRing F] [i
nst_1 : Ring K] [inst_2 : Algebra F K] (x : K),   IsSeparable F x = (minpoly F x
).Sepa…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FixedPoints.minpoly_eq_minpoly`：minpoly_eq_minpoly : minpoly G F x = _ro
ot_.minpoly (FixedPoints.subfield G F) x
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FixedPoints.minpoly.eq_1`：∀ (G : Type u) [inst : Group G] (F : Type v) [
inst_1 : Field F] [inst_2 : MulSemiringAction G F] [inst_3 : Fintype G]   (x : F
), FixedPoints…
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subfield.toSubring_subtype_eq_subtype`：toSubring_subtype_eq_subtype (S :
 Subfield K) : S.toSubring.subtype = S.subtype
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.separable_prod_X_sub_C_iff`：separable_prod_X_sub_C_iff {ι : S
ort _} [Fintype ι] {f : ι -> F} : (∏ i, (X - C (f i))).Separable ↔ Function.Inje
ctive f
· 使用定理 `MulAction.injective_ofQuotientStabilizer`：injective_ofQuotientStabilizer
 : Function.Injective (ofQuotientStabilizer G x)
-/
instance isSeparable : Algebra.IsSeparable (FixedPoints.subfield G F) F := by
  classical
  exact ⟨fun x => by
    cases nonempty_fintype G
    rw [IsSeparable, ← minpoly_eq_minpoly,
      ← Polynomial.separable_map (FixedPoints.subfield G F).subtype, minpoly,
      ← Subfield.toSubring_subtype_eq_subtype, Polynomial.map_toSubring _ (subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_ofQuotientStabilizer G x)⟩
/-
**FixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FiniteDimensional (subfield G F) F := by
  cases nonempty_fintype G
  exact IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt Cardinal.natCast_lt_aleph0)

end Finite

/-
**FixedPoints.finrank_le_card** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：finrank_le_card [Fintype G] : finrank (subfield G F) F <= Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FixedPoints.instFiniteDimensionalSubtypeMemSubfieldSubfield`：∀ (G : Type
 u) [inst : Group G] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction
 G F] [Finite G],   FiniteDimensional (↥(FixedPoi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FixedPoints.rank_le_card`：rank_le_card : Module.rank (FixedPoints.subfie
ld G F) F <= Fintype.card G
-/
theorem finrank_le_card [Fintype G] : finrank (subfield G F) F ≤ Fintype.card G := by
  rw [← @Nat.cast_le Cardinal, finrank_eq_rank]
  apply rank_le_card

end FixedPoints

/-
**linearIndependent_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_toLinearMap (R : Type u) (A : Type v) (B : Type w) [Comm
Semiring R] [Semiring A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B] :
 LinearIndependent B (AlgHom.toLinearMap : (A ->ₐ[R] B) -> A ->ₗ[R] B)
参数：R : Type u；A : Type v；B : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `linearIndependent_monoidHom`：linearIndependent_monoidHom (G : Type*) [Mu
lOneClass G] (L : Type*) [CommRing L] [IsDomain L] : LinearIndependent L (M
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
-/
theorem linearIndependent_toLinearMap (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A →ₐ[R] B) → A →ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A →ₐ[R] B) → A →* B) fun _ _ hfg =>
        AlgHom.ext fun _ => DFunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _
/-
**cardinalMk_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinalMk_algHom (K : Type u) (V : Type v) (W : Type w) [Field K] [Ring V
] [Algebra K V] [FiniteDimensional K V] [Field W] [Algebra K W] : Cardinal.mk (V
 ->ₐ[K] W) <= finrank W (V ->ₗ[K] W)
参数：K : Type u；V : Type v；W : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.cardinalMk_le_finrank`：cardinalMk_le_finrank [Module.F
inite R M] {ι : Type w} {b : ι -> M} (h : LinearIndependent R b) : #ι <= finrank
 R M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `linearIndependent_toLinearMap`：linearIndependent_toLinearMap (R : Type u
) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Algebra R A] [CommRin
g B] [IsDomain B] […
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem cardinalMk_algHom (K : Type u) (V : Type v) (W : Type w) [Field K] [Ring V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] :
    Cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
  (linearIndependent_toLinearMap K V W).cardinalMk_le_finrank
/-
**AlgEquiv.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K 
V] [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V)
参数：K : Type u；V : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V →ₐ[K] V) (algEquivEquivAlgHom K V).symm
/-
**finrank_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_algHom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
 [FiniteDimensional K V] : Fintype.card (V ->ₐ[K] V) <= finrank V (V ->ₗ[K] V)
参数：K : Type u；V : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.fintype_card_le_finrank`：fintype_card_le_finrank [Modu
le.Finite R M] {ι : Type*} [Fintype ι] {b : ι -> M} (h : LinearIndependent R b) 
: Fintype.card ι <= finrank R M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `linearIndependent_toLinearMap`：linearIndependent_toLinearMap (R : Type u
) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Algebra R A] [CommRin
g B] [IsDomain B] […
-/
theorem finrank_algHom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
  (linearIndependent_toLinearMap K V V).fintype_card_le_finrank
/-
**AlgHom.card_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDime
nsional F K] : Fintype.card (K ->ₐ[F] K) <= Module.finrank F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `finrank_algHom`：finrank_algHom (K : Type u) (V : Type v) [Field K] [Fiel
d V] [Algebra K V] [FiniteDimensional K V] : Fintype.card (V ->ₐ[K] V) <= finran
k V …
· 使用定理 `Module.finrank_linearMap_self`：Module.finrank_linearMap_self : finrank S
 (M ->ₗ[R] S) = finrank R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem AlgHom.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K →ₐ[F] K) ≤ Module.finrank F K :=
  Module.finrank_linearMap_self F K K ▸ finrank_algHom F K
/-
**AlgEquiv.card_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDi
mensional F K] : Fintype.card Gal(K/F) <= Module.finrank F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHom.card_le`：AlgHom.card_le {F K : Type*} [Field F] [Field K] [Algebr
a F K] [FiniteDimensional F K] : Fintype.card (K ->ₐ[F] K) <= Module.finrank F K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
-/
theorem AlgEquiv.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card Gal(K/F) ≤ Module.finrank F K :=
  Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le

namespace FixedPoints

variable (G F : Type*) [Group G] [Field F] [MulSemiringAction G F]

/-- Let $F$ be a field. Let $G$ be a finite group acting faithfully on $F$.
Then $[F : F^G] = |G|$. -/
@[stacks 09I3 "second part"]
/-
**FixedPoints.finrank_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：finrank_eq_card [Fintype G] [FaithfulSMul G F] : finrank (FixedPoints.subf
ield G F) F = Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `FixedPoints.finrank_le_card`：finrank_le_card [Fintype G] : finrank (subf
ield G F) F <= Fintype.card G
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `FixedPoints.instFiniteDimensionalSubtypeMemSubfieldSubfield`：∀ (G : Type
 u) [inst : Group G] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction
 G F] [Finite G],   FiniteDimensional (↥(FixedPoi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
· 使用定理 `MulSemiringAction.toAlgHom_injective`：toAlgHom_injective [FaithfulSMul M
 A] : Function.Injective (MulSemiringAction.toAlgHom R A : M -> A ->ₐ[R] A)
· 使用定理 `finrank_algHom`：finrank_algHom (K : Type u) (V : Type v) [Field K] [Fiel
d V] [Algebra K V] [FiniteDimensional K V] : Fintype.card (V ->ₐ[K] V) <= finran
k V …
· 使用定理 `Module.finrank_linearMap_self`：Module.finrank_linearMap_self : finrank S
 (M ->ₗ[R] S) = finrank R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
Let $F$ be a field. Let $G$ be a finite group acting faithfully on $F$.
Then $[F : F^G] = |G|$.
-/
theorem finrank_eq_card [Fintype G] [FaithfulSMul G F] :
    finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  le_antisymm (FixedPoints.finrank_le_card G F) <|
    calc
      Fintype.card G ≤ Fintype.card (F →ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ ≤ finrank F (F →ₗ[FixedPoints.subfield G F] F) := finrank_algHom (subfield G F) F
      _ = finrank (FixedPoints.subfield G F) F := finrank_linearMap_self _ _ _

/-- `MulSemiringAction.toAlgHom` is bijective. -/
/-
**FixedPoints.toAlgHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：toAlgHom_bijective [Finite G] [FaithfulSMul G F] : Function.Bijective (Mul
SemiringAction.toAlgHom _ _ : G -> F ->ₐ[subfield G F] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `FixedPoints.instFiniteDimensionalSubtypeMemSubfieldSubfield`：∀ (G : Type
 u) [inst : Group G] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction
 G F] [Finite G],   FiniteDimensional (↥(FixedPoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `MulSemiringAction.toAlgHom_injective`：toAlgHom_injective [FaithfulSMul M
 A] : Function.Injective (MulSemiringAction.toAlgHom R A : M -> A ->ₐ[R] A)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FixedPoints.finrank_eq_card`：finrank_eq_card [Fintype G] [FaithfulSMul G
 F] : finrank (FixedPoints.subfield G F) F = Fintype.card G
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `finrank_algHom`：finrank_algHom (K : Type u) (V : Type v) [Field K] [Fiel
d V] [Algebra K V] [FiniteDimensional K V] : Fintype.card (V ->ₐ[K] V) <= finran
k V …
· 使用定理 `Module.finrank_linearMap_self`：Module.finrank_linearMap_self : finrank S
 (M ->ₗ[R] S) = finrank R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
`MulSemiringAction.toAlgHom` is bijective.
-/
theorem toAlgHom_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgHom _ _ : G → F →ₐ[subfield G F] F) := by
  cases nonempty_fintype G
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.toAlgHom_injective _ F
  · apply le_antisymm
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
    · rw [← finrank_eq_card G F]
      exact LE.le.trans_eq (finrank_algHom _ F) (finrank_linearMap_self _ _ _)

/-- Bijection between `G` and algebra endomorphisms of `F` that fix the fixed points. -/
/-
**FixedPoints.toAlgHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FixedPoints`。
形式化陈述：toAlgHomEquiv [Finite G] [FaithfulSMul G F] : G ≃ (F ->ₐ[FixedPoints.subfi
eld G F] F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FixedPoints.toAlgHom_bijective`：toAlgHom_bijective [Finite G] [FaithfulS
Mul G F] : Function.Bijective (MulSemiringAction.toAlgHom _ _ : G -> F ->ₐ[subfi
eld G F] F)

--- 原说明 ---
Bijection between `G` and algebra endomorphisms of `F` that fix the fixed points
.
-/
def toAlgHomEquiv [Finite G] [FaithfulSMul G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equiv.ofBijective _ (toAlgHom_bijective G F)

/-- `MulSemiringAction.toAlgAut` is bijective. -/
/-
**FixedPoints.toAlgAut_bijective** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：toAlgAut_bijective [Finite G] [FaithfulSMul G F] : Function.Bijective (Mul
SemiringAction.toAlgAut G (FixedPoints.subfield G F) F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `FixedPoints.toAlgHom_bijective`：toAlgHom_bijective [Finite G] [FaithfulS
Mul G F] : Function.Bijective (MulSemiringAction.toAlgHom _ _ : G -> F ->ₐ[subfi
eld G F] F)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f

--- 原说明 ---
`MulSemiringAction.toAlgAut` is bijective.
-/
theorem toAlgAut_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  refine ⟨fun _ _ h ↦ (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f ↦ ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h ↦ ?_)⟩ <;>
      rwa [DFunLike.ext_iff] at h ⊢

/-- Bijection between `G` and algebra automorphisms of `F` that fix the fixed points. -/
/-
**FixedPoints.toAlgAutMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FixedPoints`。
形式化陈述：toAlgAutMulEquiv [Finite G] [FaithfulSMul G F] : G ≃* (F ≃ₐ[FixedPoints.su
bfield G F] F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FixedPoints.toAlgAut_bijective`：toAlgAut_bijective [Finite G] [FaithfulS
Mul G F] : Function.Bijective (MulSemiringAction.toAlgAut G (FixedPoints.subfiel
d G F) F)

--- 原说明 ---
Bijection between `G` and algebra automorphisms of `F` that fix the fixed points
.
-/
def toAlgAutMulEquiv [Finite G] [FaithfulSMul G F] : G ≃* (F ≃ₐ[FixedPoints.subfield G F] F) :=
  MulEquiv.ofBijective _ (toAlgAut_bijective G F)

/-- `MulSemiringAction.toAlgAut` is surjective. -/
/-
**FixedPoints.toAlgAut_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FixedPoints`。
形式化陈述：toAlgAut_surjective [Finite G] : Function.Surjective (MulSemiringAction.to
AlgAut G (FixedPoints.subfield G F) F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
· 使用定理 `AlgEquiv.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A
] [inst_…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `FixedPoints.toAlgAut_bijective`：toAlgAut_bijective [Finite G] [FaithfulS
Mul G F] : Function.Bijective (MulSemiringAction.toAlgAut G (FixedPoints.subfiel
d G F) F)
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FixedPoints.instFiniteDimensionalSubtypeMemSubfieldSubfield`：∀ (G : Type
 u) [inst : Group G] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction
 G F] [Finite G],   FiniteDimensional (↥(FixedPoi…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x

--- 原说明 ---
`MulSemiringAction.toAlgAut` is surjective.
-/
theorem toAlgAut_surjective [Finite G] :
    Function.Surjective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  let f : G →* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.compHom _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨fun {q₁ q₂} ↦ by
    induction q₁, q₂ using Quotient.inductionOn₂ with | _ g₁ g₂
    intro h
    rwa [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  intro f
  obtain ⟨q, hq⟩ := (toAlgAut_bijective Q F).surjective
    (AlgEquiv.ofRingEquiv (f := f) (fun ⟨x, hx⟩ ↦ f.commutes' ⟨x, fun g ↦ hx g⟩))
  revert hq
  refine QuotientGroup.induction_on q (fun g hg ↦ ⟨g, ?_⟩)
  rwa [AlgEquiv.ext_iff] at hg ⊢

end FixedPoints

