/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous subsemirings of a graded semiring

This file defines homogeneous subsemirings of a graded semiring, as well as operations on them.

## Main definitions

* `HomogeneousSubsemiring 𝒜`: The type of subsemirings which satisfy `SetLike.IsHomogeneous`.
-/

@[expose] public section

open DirectSum Set SetLike

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [DecidableEq ι] [GradedRing 𝒜]
variable (R : Subsemiring A)

section HomogeneousDef

variable {R} in
/-
**DirectSum.SetLike.IsHomogeneous.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.SetLike.IsHomogeneous.mem_iff (hR : IsHomogeneous 𝒜 R) {a} : a i
n R ↔ forall i, (decompose 𝒜 a i : A) in R
参数：hR : IsHomogeneous 𝒜 R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff`：∀ {ι : Type u_1} {M :
 Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [ins
t_2 : SetLike σ M]   [inst_3 : AddSubmo…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem DirectSum.SetLike.IsHomogeneous.mem_iff (hR : IsHomogeneous 𝒜 R) {a} :
    a ∈ R ↔ ∀ i, (decompose 𝒜 a i : A) ∈ R :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

/-- A `HomogeneousSubsemiring` is a `Subsemiring` that satisfies `IsHomogeneous`. -/
/-
**HomogeneousSubsemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {σ : Type u_2} →     {A : Type u_3} →       [inst : Add
Monoid ι] →         [inst_1 : Semiring A] →           [inst_2 : SetLike σ A] →  
           [inst_3 : AddSubmonoidClass σ A] → (𝒜 : ι → σ) → [inst_4 : DecidableE
q ι] → [GradedRing 𝒜] → Type u_3
参数：𝒜 : ι → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomogeneousSubsemiring` is a `Subsemiring` that satisfies `IsHomogeneous`.
-/
structure HomogeneousSubsemiring extends Subsemiring A where
  is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring

variable {𝒜}

namespace HomogeneousSubsemiring

/-
**HomogeneousSubsemiring.toSubsemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousSubsemiring`。
形式化陈述：toSubsemiring_injective : (toSubsemiring : HomogeneousSubsemiring 𝒜 -> Sub
semiring A).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousSubsemiring.mk.congr_simp`：∀ {ι : Type u_1} {σ : Type u_2} {A
 : Type u_3} [inst : AddMonoid ι] [inst_1 : Semiring A] [inst_2 : SetLike σ A]  
 [inst_3 : AddSubmonoidCla…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSubsemiring_injective :
    (toSubsemiring : HomogeneousSubsemiring 𝒜 → Subsemiring A).Injective :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]
/-
**HomogeneousSubsemiring.setLike** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousSubsemiri
ng`。
形式化陈述：setLike : SetLike (HomogeneousSubsemiring 𝒜) A where coe x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (HomogeneousSubsemiring 𝒜) A where
  coe x := x.carrier
  coe_injective _ _ h := toSubsemiring_injective <| SetLike.coe_injective h
/-
**HomogeneousSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (HomogeneousSubsemiring 𝒜) := .ofSetLike (HomogeneousSubsemiring 𝒜) A
/-
**HomogeneousSubsemiring.isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousSub
semiring`。
形式化陈述：isHomogeneous (R : HomogeneousSubsemiring 𝒜) : IsHomogeneous 𝒜 R
参数：R : HomogeneousSubsemiring 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubsemiring.is_homogeneous'`：∀ {ι : Type u_1} {σ : Type u_2} 
{A : Type u_3} [inst : AddMonoid ι] [inst_1 : Semiring A] [inst_2 : SetLike σ A]
   [inst_3 : AddSubmonoidCla…
-/
theorem isHomogeneous (R : HomogeneousSubsemiring 𝒜) :
    IsHomogeneous 𝒜 R := R.is_homogeneous'
/-
**HomogeneousSubsemiring.subsemiringClass** 是 Mathlib 中的一个实例，位于命名空间 `Homogeneous
Subsemiring`。
形式化陈述：subsemiringClass : SubsemiringClass (HomogeneousSubsemiring 𝒜) A where mul
_mem {a}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mul_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R) {x y : R}, x ∈ s → y ∈ s → x * y ∈ s
· 使用定理 `Subsemiring.one_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R), 1 ∈ s
· 使用定理 `Subsemiring.add_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R) {x y : R}, x ∈ s → y ∈ s → x + y ∈ s
· 使用定理 `Subsemiring.zero_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Su
bsemiring R), 0 ∈ s
-/
instance subsemiringClass : SubsemiringClass (HomogeneousSubsemiring 𝒜) A where
  mul_mem {a} := a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]
/-
**HomogeneousSubsemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousSubsemiring`。
形式化陈述：ext {R S : HomogeneousSubsemiring 𝒜} (h : R.toSubsemiring = S.toSubsemirin
g) : R = S
参数：h : R.toSubsemiring = S.toSubsemiring。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubsemiring.toSubsemiring_injective`：toSubsemiring_injective 
: (toSubsemiring : HomogeneousSubsemiring 𝒜 -> Subsemiring A).Injective
-/
theorem ext {R S : HomogeneousSubsemiring 𝒜}
    (h : R.toSubsemiring = S.toSubsemiring) : R = S :=
  HomogeneousSubsemiring.toSubsemiring_injective h
/-
**HomogeneousSubsemiring.ext'** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousSubsemiring`
。
形式化陈述：ext' {R S : HomogeneousSubsemiring 𝒜} (h : forall i, forall a in 𝒜 i, a in
 R ↔ a in S) : R = S
参数：h : forall i, forall a in 𝒜 i, a in R ↔ a in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.AddSubmonoidClass.IsHomogeneous.ext`：∀ {ι : Type u_1} {M : Typ
e u_3} {σ : Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 
: SetLike σ M]   [inst_3 : AddSubmo…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `HomogeneousSubsemiring.is_homogeneous'`：∀ {ι : Type u_1} {σ : Type u_2} 
{A : Type u_3} [inst : AddMonoid ι] [inst_1 : Semiring A] [inst_2 : SetLike σ A]
   [inst_3 : AddSubmonoidCla…
-/
theorem ext' {R S : HomogeneousSubsemiring 𝒜}
    (h : ∀ i, ∀ a ∈ 𝒜 i, a ∈ R ↔ a ∈ S) : R = S :=
  AddSubmonoidClass.IsHomogeneous.ext R.2 S.2 h

@[simp high]
/-
**HomogeneousSubsemiring.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousSubsemiri
ng`。
形式化陈述：mem_iff {R : HomogeneousSubsemiring 𝒜} {a} : a in R.toSubsemiring ↔ a in R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {R : HomogeneousSubsemiring 𝒜} {a} :
    a ∈ R.toSubsemiring ↔ a ∈ R :=
  Iff.rfl

end HomogeneousSubsemiring

set_option backward.isDefEq.respectTransparency false in
/-
**IsHomogeneous.subsemiringClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHomogeneous.subsemiringClosure {s : Set A} (h : forall (i : ι) ⦃x : A⦄, 
x in s -> (decompose 𝒜 x i : A) in s) : IsHomogeneous 𝒜 (Subsemiring.closure s)
参数：h : forall (i : ι) ⦃x : A⦄, x in s -> (decompose 𝒜 x i : A) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.closure_induction`：closure_induction {s : Set R} {p : (x : R
) -> x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_closur
e hx)) (zero : p 0 …
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decompose_zero`：decompose_zero : decompose ℳ (0 : M) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `DirectSum.decompose_one`：decompose_one : decompose 𝒜 (1 : A) = 1
· 使用定理 `DirectSum.one_def`：one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `DirectSum.decompose_add`：decompose_add (x y : M) : decompose ℳ (x + y) =
 decompose ℳ x + decompose ℳ y
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.mul_eq_dfinsuppSum`：mul_eq_dfinsuppSum [forall (i : ι) (x : A 
i), Decidable (x != 0)] (a a' : ⨁ i, A i) : a * a' = a.sum fun _ ai => a'.sum fu
n _ aj => DirectSu…
· 使用定理 `DFinsupp.sum_apply`：sum_apply {ι} {β : ι -> Type v} {ι₁ : Type u₁} [Deci
dableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i
), Decid…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
（共 35 条，此处仅展示前 30 条）
-/
theorem IsHomogeneous.subsemiringClosure {s : Set A}
    (h : ∀ (i : ι) ⦃x : A⦄, x ∈ s → (decompose 𝒜 x i : A) ∈ s) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := fun i x hx ↦ by
  induction hx using Subsemiring.closure_induction generalizing i with
  | mem _ hx => exact Subsemiring.subset_closure <| h i hx
  | zero => simp
  | one =>
    rw [decompose_one, one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | mul x y _ _ h₁ h₂ =>
    classical
    rw [decompose_mul, DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun j _ ↦ ?_
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun k _ ↦ ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]
/-
**IsHomogeneous.subsemiringClosure_of_isHomogeneousElem** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：IsHomogeneous.subsemiringClosure_of_isHomogeneousElem {s : Set A} (h : for
all x in s, IsHomogeneousElem 𝒜 x) : IsHomogeneous 𝒜 (Subsemiring.closure s)
参数：h : forall x in s, IsHomogeneousElem 𝒜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_insert_zero`：closure_insert_zero (s : Set R) : closu
re (insert 0 s) = closure s
· 使用定理 `IsHomogeneous.subsemiringClosure`：IsHomogeneous.subsemiringClosure {s : 
Set A} (h : forall (i : ι) ⦃x : A⦄, x in s -> (decompose 𝒜 x i : A) in s) : IsHo
mogeneous 𝒜 (Subsemiri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decompose_zero`：decompose_zero : decompose ℳ (0 : M) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem IsHomogeneous.subsemiringClosure_of_isHomogeneousElem {s : Set A}
    (h : ∀ x ∈ s, IsHomogeneousElem 𝒜 x) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := by
  rw [← Subsemiring.closure_insert_zero s]
  refine IsHomogeneous.subsemiringClosure fun i x hx ↦ ?_
  obtain rfl | hx := mem_insert_iff.mp hx
  · simp
  · obtain ⟨j, hj⟩ := h x hx
    obtain rfl | h := eq_or_ne i j <;> simp [decompose_of_mem _ hj, of_eq_of_ne, *]

end HomogeneousDef

section HomogeneousCore

/-- For any subsemiring `R`, not necessarily homogeneous, `R.homogeneousCore 𝒜` is the largest
homogeneous subsemiring contained in `R`. -/
/-
**Subsemiring.homogeneousCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemiring.homogeneousCore : HomogeneousSubsemiring 𝒜 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any subsemiring `R`, not necessarily homogeneous, `R.homogeneousCore 𝒜` is t
he largest
homogeneous subsemiring contained in `R`.
-/
def Subsemiring.homogeneousCore : HomogeneousSubsemiring 𝒜 where
  __ := Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) → A) ⁻¹' R))
  is_homogeneous' := IsHomogeneous.subsemiringClosure_of_isHomogeneousElem fun x ↦ by
    rintro ⟨x, _, rfl⟩; exact x.2
/-
**Subsemiring.homogeneousCore_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.homogeneousCore_mono : Monotone (Subsemiring.homogeneousCore 𝒜
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) 
: closure s <= closure t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem Subsemiring.homogeneousCore_mono : Monotone (Subsemiring.homogeneousCore 𝒜) :=
  fun _ _ h => Subsemiring.closure_mono <| Set.image_mono <| fun _ ↦ @h _
/-
**Subsemiring.toSubsemiring_homogeneousCore_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.toSubsemiring_homogeneousCore_le : (R.homogeneousCore 𝒜).toSub
semiring <= R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem Subsemiring.toSubsemiring_homogeneousCore_le : (R.homogeneousCore 𝒜).toSubsemiring ≤ R :=
  Subsemiring.closure_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubsemiringDefs

/-
**Subsemiring.isHomogeneous_iff_forall_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.isHomogeneous_iff_forall_subset : SetLike.IsHomogeneous 𝒜 R ↔ 
forall i, (R : Set A) subseteq GradedRing.proj 𝒜 i ⁻¹' (R : Set A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Subsemiring.isHomogeneous_iff_forall_subset :
    SetLike.IsHomogeneous 𝒜 R ↔ ∀ i, (R : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' (R : Set A) :=
  Iff.rfl
/-
**Subsemiring.isHomogeneous_iff_subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.isHomogeneous_iff_subset_iInter : SetLike.IsHomogeneous 𝒜 R ↔ 
(R : Set A) subseteq ⋂ i, GradedRing.proj 𝒜 i ⁻¹' R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.subset_iInter_iff`：subset_iInter_iff {s : Set α} {t : ι -> Set α} : 
(s subseteq ⋂ i, t i) ↔ forall i, s subseteq t i
-/
theorem Subsemiring.isHomogeneous_iff_subset_iInter :
    SetLike.IsHomogeneous 𝒜 R ↔ (R : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' R :=
  subset_iInter_iff.symm

end IsHomogeneousSubsemiringDefs

