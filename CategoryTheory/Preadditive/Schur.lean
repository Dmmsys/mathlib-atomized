/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Schur's lemma

We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite-dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category* C]
variable [Preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `Preadditive C`.
/-
**CategoryTheory.mono_of_nonzero_from_simple** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y
} (w : f != 0) : Mono f
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_kernel_zero`：mono_of_kernel_zero {X Y
 : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w : kernel.ι f = 0) : Mono f
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.kernel_zero_of_nonzero_from_simple`：kernel_zero_of_nonzer
o_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f] (w : f != 0) : kern
el.ι f = 0
-/
theorem mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f ≠ 0) :
    Mono f :=
  Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

/-- The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
/-
**CategoryTheory.isIso_of_hom_simple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_of_hom_simple [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X 
⟶ Y} (w : f != 0) : IsIso f
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_mono_of_nonzero`：isIso_of_mono_of_nonzero {X Y :
 C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f
· 使用定理 `CategoryTheory.mono_of_nonzero_from_simple`：mono_of_nonzero_from_simple 
[HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f != 0) : Mono f

--- 原说明 ---
The part of **Schur's lemma** that holds in any preadditive category with kernel
s:
that a nonzero morphism between simple objects is an isomorphism.
-/
theorem isIso_of_hom_simple
    [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : IsIso f :=
  haveI := mono_of_nonzero_from_simple w
  isIso_of_mono_of_nonzero w

/-- As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
/-
**CategoryTheory.isIso_iff_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ 
Y) : IsIso f ↔ f != 0
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.id_nonzero`：id_nonzero (X : C) [Simple.{v} X] : 𝟙 X != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.isIso_of_hom_simple`：isIso_of_hom_simple [HasKernels C] {
X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f != 0) : IsIso f

--- 原说明 ---
As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or ze
ro.
-/
theorem isIso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y) :
    IsIso f ↔ f ≠ 0 :=
  ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← IsIso.hom_inv_id f, h, zero_comp],
   fun w => isIso_of_hom_simple w⟩

open scoped Classical in
/-- In any preadditive category with kernels,
the endomorphisms of a simple object form a division ring. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In any preadditive category with kernels,
the endomorphisms of a simple object form a division ring.
-/
noncomputable instance [HasKernels C] {X : C} [Simple X] : DivisionRing (End X) where
  inv f := if h : f = 0 then 0 else haveI := isIso_of_hom_simple h; inv f
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩
  inv_zero := dif_pos rfl
  mul_inv_cancel f hf := by
    dsimp
    rw [dif_neg hf]
    have := isIso_of_hom_simple hf
    exact IsIso.inv_hom_id f
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

open Module

section

variable (𝕜 : Type*) [DivisionRing 𝕜]

/-- Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
/-
**CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory`。
形式化陈述：finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {
X Y : C} [Simple X] [Simple Y] (h : (X ≅ Y) -> False) : finrank 𝕜 (X ⟶ Y) = 0
参数：h : (X ≅ Y) -> False。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_zero_of_subsingleton`：Module.finrank_zero_of_subsingleton
 [Subsingleton M] : finrank R M = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `CategoryTheory.isIso_iff_nonzero`：isIso_iff_nonzero [HasKernels C] {X Y 
: C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {X Y : C}
    [Simple X] [Simple Y] (h : (X ≅ Y) → False) : finrank 𝕜 (X ⟶ Y) = 0 :=
  haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton

end

variable (𝕜 : Type*) [Field 𝕜]
variable [IsAlgClosed 𝕜] [Linear 𝕜 C]

set_option backward.isDefEq.respectTransparency false in
-- We prove this with the explicit `isIso_iff_nonzero` assumption,
-- rather than just `[Simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
/-- An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
/-
**CategoryTheory.finrank_endomorphism_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：finrank_endomorphism_eq_one {X : C} (isIso_iff_nonzero : forall f : X ⟶ X,
 IsIso f ↔ f != 0) [I : FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1
参数：isIso_iff_nonzero : forall f : X ⟶ X, IsIso f ↔ f != 0；X ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finrank_eq_one`：finrank_eq_one (v : M) (n : v != 0) (h : forall w : M, e
xists c : R, c • v = w) : finrank R M = 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`：nonempty_of_isAlg
Closed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A] [I : FiniteDimensiona
l 𝕜 A] (a : A) : (σ a).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `CategoryTheory.isUnit_iff_isIso`：isUnit_iff_isIso {C : Type u} [Category
.{v} C] {X : C} (f : End X) : IsUnit (f : End X) ↔ IsIso f
· 使用定理 `IsUnit.sub_iff`：IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsU
nit (y - x)
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)

--- 原说明 ---
An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
theorem finrank_endomorphism_eq_one {X : C} (isIso_iff_nonzero : ∀ f : X ⟶ X, IsIso f ↔ f ≠ 0)
    [I : FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1 := by
  have id_nonzero := (isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  refine finrank_eq_one (𝟙 X) id_nonzero ?_
  intro f
  have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
  have : FiniteDimensional 𝕜 (End X) := I
  obtain ⟨c, nu⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional 𝕜 (End.of f)
  use c
  rw [spectrum.mem_iff, IsUnit.sub_iff, isUnit_iff_isIso, isIso_iff_nonzero, Ne,
    Classical.not_not, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at nu
  exact nu.symm

variable [HasKernels C]

/-- **Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
/-
**CategoryTheory.finrank_endomorphism_simple_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：finrank_endomorphism_simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜
 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1
参数：X : C；X ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.finrank_endomorphism_eq_one`：finrank_endomorphism_eq_one 
{X : C} (isIso_iff_nonzero : forall f : X ⟶ X, IsIso f ↔ f != 0) [I : FiniteDime
nsional 𝕜 (X ⟶ X)] : finrank 𝕜 (…
· 使用定理 `CategoryTheory.isIso_iff_nonzero`：isIso_iff_nonzero [HasKernels C] {X Y 
: C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f != 0

--- 原说明 ---
**Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero
/-
**CategoryTheory.endomorphism_simple_eq_smul_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：endomorphism_simple_eq_smul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X 
⟶ X)] (f : X ⟶ X) : exists c : 𝕜, c • 𝟙 X = f
参数：X ⟶ X；f : X ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `CategoryTheory.id_nonzero`：id_nonzero (X : C) [Simple.{v} X] : 𝟙 X != 0
· 使用定理 `CategoryTheory.finrank_endomorphism_simple_eq_one`：finrank_endomorphism_
simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ 
X) = 1
-/
theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
    (f : X ⟶ X) : ∃ c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f

/-- Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `𝕜` would be undetermined.
-/
@[instance_reducible]
/-
**CategoryTheory.fieldEndOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：fieldEndOfFiniteDimensional (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X
 ⟶ X)] : Field (End X)
参数：X : C；X ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `𝕜` would be undetermined.
-/
noncomputable def fieldEndOfFiniteDimensional (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)] :
    Field (End X) := by
  exact
    { (inferInstance : DivisionRing (End X)) with
      mul_comm := fun f g => by
        obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f
        obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g
        simp [← mul_smul, mul_comm c d] }

-- There is a symmetric argument that uses `[FiniteDimensional 𝕜 (Y ⟶ Y)]` instead,
-- but we don't bother proving that here.
/-- **Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
/-
**CategoryTheory.finrank_hom_simple_simple_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [
Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) <= 1
参数：X Y : C；X ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_zero_of_subsingleton`：Module.finrank_zero_of_subsingleton
 [Subsingleton M] : finrank R M = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isIso_iff_nonzero`：isIso_iff_nonzero [HasKernels C] {X Y 
: C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f != 0
· 使用定理 `finrank_le_one`：finrank_le_one (v : M) (h : forall w : M, exists c : R, 
c • v = w) : finrank R M <= 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `CategoryTheory.endomorphism_simple_eq_smul_id`：endomorphism_simple_eq_sm
ul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) : exists c : 
𝕜, c • 𝟙 X = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h

--- 原说明 ---
**Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at m
ost 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zer
o_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
theorem finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) ≤ 1 := by
  obtain (h | h) := subsingleton_or_nontrivial (X ⟶ Y)
  · rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    have fi := (isIso_iff_nonzero f).mpr nz
    refine finrank_le_one f ?_
    intro g
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f)
    exact ⟨c, by simpa using w =≫ f⟩
/-
**CategoryTheory.finrank_hom_simple_simple_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
形式化陈述：finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X
)] [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) = 1 ↔
 Nonempty (X ≅ Y)
参数：X Y : C；X ⟶ X；X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_eq_one_iff'`：finrank_eq_one_iff' [Module.Free K V] : finrank K V
 = 1 ↔ exists v != 0, forall w : V, exists c : K, c • v = w
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_iff_nonzero`：isIso_iff_nonzero [HasKernels C] {X Y 
: C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f != 0
· 使用定理 `CategoryTheory.finrank_hom_simple_simple_le_one`：finrank_hom_simple_simp
le_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X] [Simple Y] : finran
k 𝕜 (X ⟶ Y) <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff_exists_ne_zero`：Module.finrank_pos_iff_exists_ne_
zero [IsDomain R] [IsTorsionFree R M] : 0 < finrank R M ↔ exists x : M, x != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 1 ↔ Nonempty (X ≅ Y) := by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← isIso_iff_nonzero] at nz
    exact ⟨asIso f⟩
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (isIso_iff_nonzero f.hom).mp inferInstance⟩
    lia
/-
**CategoryTheory.finrank_hom_simple_simple_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ 
X)] [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) = 0 
↔ IsEmpty (X ≅ Y)
参数：X Y : C；X ⟶ X；X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `CategoryTheory.finrank_hom_simple_simple_eq_one_iff`：finrank_hom_simple_
simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [FiniteDimensional 𝕜 (
X ⟶ Y)] [Simple X] [Simple Y] : finrank 𝕜…
· 使用定理 `CategoryTheory.finrank_hom_simple_simple_le_one`：finrank_hom_simple_simp
le_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X] [Simple Y] : finran
k 𝕜 (X ⟶ Y) <= 1
-/
theorem finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 0 ↔ IsEmpty (X ≅ Y) := by
  rw [← not_nonempty_iff, ← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  lia

open scoped Classical in
/-
**CategoryTheory.finrank_hom_simple_simple** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：finrank_hom_simple_simple (X Y : C) [forall X Y : C, FiniteDimensional 𝕜 (
X ⟶ Y)] [Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) = if Nonempty (X ≅ Y) then 1 e
lse 0
参数：X Y : C；X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.finrank_hom_simple_simple_eq_one_iff`：finrank_hom_simple_
simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [FiniteDimensional 𝕜 (
X ⟶ Y)] [Simple X] [Simple Y] : finrank 𝕜…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `CategoryTheory.finrank_hom_simple_simple_eq_zero_iff`：finrank_hom_simple
_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [FiniteDimensional 𝕜
 (X ⟶ Y)] [Simple X] [Simple Y] : finrank …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem finrank_hom_simple_simple (X Y : C) [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  split_ifs with h
  · exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  · exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)

end CategoryTheory

