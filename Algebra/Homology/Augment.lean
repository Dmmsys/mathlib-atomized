/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.Single

/-!
# Augmentation and truncation of `ℕ`-indexed (co)chain complexes.
-/

@[expose] public section


noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V]

namespace ChainComplex

/-- The truncation of an `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
/-
**ChainComplex.truncate** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：truncate [HasZeroMorphisms V] : ChainComplex V Nat ⥤ ChainComplex V Nat wh
ere obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncation of an `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
def truncate [HasZeroMorphisms V] : ChainComplex V ℕ ⥤ ChainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => C.shape _ _ <| by simpa }
  map f := { f := fun i => f.f (i + 1) }

set_option backward.isDefEq.respectTransparency false in
/-- There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
/-
**ChainComplex.truncateTo** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V Nat)
 : truncate.obj C ⟶ (single₀ V).obj (C.X 0)
参数：C : ChainComplex V Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in 
degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
def truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V ℕ) :
    truncate.obj C ⟶ (single₀ V).obj (C.X 0) :=
  (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by simp⟩

-- PROJECT when `V` is abelian (but not generally?)
-- `[∀ n, Exact (C.d (n+2) (n+1)) (C.d (n+1) n)] [Epi (C.d 1 0)]` iff `QuasiIso (C.truncate_to)`
variable [HasZeroMorphisms V]

/-- We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
/-
**ChainComplex.augment** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (C : ChainComplex V ℕ) →     
    {X : V} → (f : C.X 0 ⟶ X) → CategoryTheory.CategoryStruct.comp (C.d 1 0) f =
 0 → ChainComplex V ℕ
参数：C : ChainComplex V ℕ；f : C.X 0 ⟶ X；C.d 1 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    ChainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape
    | 1, 0, h => absurd rfl h
    | _ + 2, 0, _ => rfl
    | 0, _, _ => rfl
    | i + 1, j + 1, h => by
      simp only; exact C.shape i j (Nat.succ_ne_succ_iff.1 h)
  d_comp_d'
    | _, _, 0, rfl, rfl => w
    | _, _, k + 1, rfl, rfl => C.d_comp_d _ _ _

@[simp]
/-
**ChainComplex.augment_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：augment_X_zero (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1
 0 ≫ f = 0) : (augment C f w).X 0 = X
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_X_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
/-
**ChainComplex.augment_X_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：augment_X_succ (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1
 0 ≫ f = 0) (i : Nat) : (augment C f w).X (i + 1) = C.X i
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_X_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
/-
**ChainComplex.augment_d_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：augment_d_one_zero (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C
.d 1 0 ≫ f = 0) : (augment C f w).d 1 0 = f
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_d_one_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).d 1 0 = f :=
  rfl

@[simp]
/-
**ChainComplex.augment_d_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：augment_d_succ_succ (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : 
C.d 1 0 ≫ f = 0) (i j : Nat) : (augment C f w).d (i + 1) (j + 1) = C.d i j
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0；i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem augment_d_succ_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j := by
  cases i <;> rfl

set_option backward.defeqAttrib.useBackward true in
/-- Truncating an augmented chain complex is isomorphic (with components the identity)
to the original complex.
-/
/-
**ChainComplex.truncateAugment** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：truncateAugment (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 
1 0 ≫ f = 0) : truncate.obj (augment C f w) ≅ C where hom
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncating an augmented chain complex is isomorphic (with components the identit
y)
to the original complex.
-/
def truncateAugment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext (_ | i) <;> simp
  inv_hom_id := by
    ext (_ | i) <;> simp

@[simp]
/-
**ChainComplex.truncateAugment_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：truncateAugment_hom_f (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w 
: C.d 1 0 ≫ f = 0) (i : Nat) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i)
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem truncateAugment_hom_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
/-
**ChainComplex.truncateAugment_inv_f** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：truncateAugment_inv_f (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w 
: C.d 1 0 ≫ f = 0) (i : Nat) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.ob
j (augment C f w)).X i)
参数：C : ChainComplex V Nat；f : C.X 0 ⟶ X；w : C.d 1 0 ≫ f = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem truncateAugment_inv_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
/-
**ChainComplex.chainComplex_d_succ_succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainCom
plex`。
形式化陈述：chainComplex_d_succ_succ_zero (C : ChainComplex V Nat) (i : Nat) : C.d (i 
+ 2) 0 = 0
参数：C : ChainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_succ_ne_one`：∀ (a : ℕ), a.succ.succ ≠ 1
-/
theorem chainComplex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
/-
**ChainComplex.augmentTruncate** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：augmentTruncate (C : ChainComplex V Nat) : augment (truncate.obj C) (C.d 1
 0) (C.d_comp_d _ _ _) ≅ C where hom
参数：C : ChainComplex V Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augmenting a truncated complex with the original object and morphism is isomorph
ic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : ChainComplex V ℕ) :
    augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
        | 0 | 1 | n + 2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
          | 0 | 1 | n + 2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  hom_inv_id := by
    ext i
    cases i <;> simp
  inv_hom_id := by
    ext i
    cases i <;> simp

@[simp]
/-
**ChainComplex.augmentTruncate_hom_f_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainComple
x`。
形式化陈述：augmentTruncate_hom_f_zero (C : ChainComplex V Nat) : (augmentTruncate C).
hom.f 0 = 𝟙 (C.X 0)
参数：C : ChainComplex V Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_hom_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/-
**ChainComplex.augmentTruncate_hom_f_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComple
x`。
形式化陈述：augmentTruncate_hom_f_succ (C : ChainComplex V Nat) (i : Nat) : (augmentTr
uncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1))
参数：C : ChainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_hom_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
/-
**ChainComplex.augmentTruncate_inv_f_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainComple
x`。
形式化陈述：augmentTruncate_inv_f_zero (C : ChainComplex V Nat) : (augmentTruncate C).
inv.f 0 = 𝟙 (C.X 0)
参数：C : ChainComplex V Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_inv_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/-
**ChainComplex.augmentTruncate_inv_f_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComple
x`。
形式化陈述：augmentTruncate_inv_f_succ (C : ChainComplex V Nat) (i : Nat) : (augmentTr
uncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1))
参数：C : ChainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_inv_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

This is the inverse construction of `truncateTo`.
-/
/-
**ChainComplex.toSingle** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

This is the inverse construction of `truncateTo`.
-/
def toSingle₀AsComplex [HasZeroObject V] (C : ChainComplex V ℕ) (X : V)
    (f : C ⟶ (single₀ V).obj X) : ChainComplex V ℕ :=
  let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

end ChainComplex

namespace CochainComplex

/-- The truncation of an `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
/-
**CochainComplex.truncate** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncate [HasZeroMorphisms V] : CochainComplex V Nat ⥤ CochainComplex V Na
t where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncation of an `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
def truncate [HasZeroMorphisms V] : CochainComplex V ℕ ⥤ CochainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

set_option backward.isDefEq.respectTransparency false in
/-- There is a canonical chain map from the truncation of a cochain complex `C` to
the "single object" cochain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 0 1` in degree 0, and zero otherwise.
-/
/-
**CochainComplex.toTruncate** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V Na
t) : (single₀ V).obj (C.X 0) ⟶ truncate.obj C
参数：C : CochainComplex V Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
There is a canonical chain map from the truncation of a cochain complex `C` to
the "single object" cochain complex consisting of the truncated object `C.X 0` i
n degree 0.
The components of this chain map are `C.d 0 1` in degree 0, and zero otherwise.
-/
def toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V ℕ) :
    (single₀ V).obj (C.X 0) ⟶ truncate.obj C :=
  (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by simp⟩

variable [HasZeroMorphisms V]

/-- We can "augment" a cochain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
/-
**CochainComplex.augment** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：augment (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 
1 = 0) : CochainComplex V Nat where X | 0 => X | i + 1 => C.X i d | 0, 1 => f | 
i + 1, j + 1 => C.d i j | _, _ => 0 shape i j s
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can "augment" a cochain complex by inserting an arbitrary object in degree ze
ro
(shifting everything else up), along with a suitable differential.
-/
def augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    CochainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape i j s := by
    rcases j with (_ | _ | j) <;> cases i <;> simp_all
  d_comp_d' i j k hij hjk := by
    have (k : ℕ) : f ≫ C.d 0 (k + 1) = 0 := by
      cases k
      · exact w
      · rw [C.shape, comp_zero]
        simp only [ComplexShape.up_Rel, zero_add]
        exact (Nat.one_lt_succ_succ _).ne
    rcases k with (_ | _ | k) <;> rcases j with (_ | _ | j) <;> cases i <;> simp [this]

@[simp]
/-
**CochainComplex.augment_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：augment_X_zero (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫
 C.d 0 1 = 0) : (augment C f w).X 0 = X
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_X_zero (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
/-
**CochainComplex.augment_X_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：augment_X_succ (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫
 C.d 0 1 = 0) (i : Nat) : (augment C f w).X (i + 1) = C.X i
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_X_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i : ℕ) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
/-
**CochainComplex.augment_d_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：augment_d_zero_one (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w :
 f ≫ C.d 0 1 = 0) : (augment C f w).d 0 1 = f
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_d_zero_one (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).d 0 1 = f :=
  rfl

@[simp]
/-
**CochainComplex.augment_d_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：augment_d_succ_succ (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w 
: f ≫ C.d 0 1 = 0) (i j : Nat) : (augment C f w).d (i + 1) (j + 1) = C.d i j
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0；i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem augment_d_succ_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Truncating an augmented cochain complex is isomorphic (with components the identity)
to the original complex.
-/
/-
**CochainComplex.truncateAugment** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncateAugment (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f 
≫ C.d 0 1 = 0) : truncate.obj (augment C f w) ≅ C where hom
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncating an augmented cochain complex is isomorphic (with components the ident
ity)
to the original complex.
-/
def truncateAugment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext i
    cases i <;> simp
  inv_hom_id := by
    ext i
    cases i <;> simp

@[simp]
/-
**CochainComplex.truncateAugment_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex
`。
形式化陈述：truncateAugment_hom_f (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (
w : f ≫ C.d 0 1 = 0) (i : Nat) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i)
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem truncateAugment_hom_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
/-
**CochainComplex.truncateAugment_inv_f** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex
`。
形式化陈述：truncateAugment_inv_f (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (
w : f ≫ C.d 0 1 = 0) (i : Nat) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.
obj (augment C f w)).X i)
参数：C : CochainComplex V Nat；f : X ⟶ C.X 0；w : f ≫ C.d 0 1 = 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem truncateAugment_inv_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
/-
**CochainComplex.cochainComplex_d_succ_succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Coch
ainComplex`。
形式化陈述：cochainComplex_d_succ_succ_zero (C : CochainComplex V Nat) (i : Nat) : C.d
 0 (i + 2) = 0
参数：C : CochainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ComplexShape.up_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRightCa
ncelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.up α).Rel i j = (i + 1 = 
j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
-/
theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
/-
**CochainComplex.augmentTruncate** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：augmentTruncate (C : CochainComplex V Nat) : augment (truncate.obj C) (C.d
 0 1) (C.d_comp_d _ _ _) ≅ C where hom
参数：C : CochainComplex V Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augmenting a truncated complex with the original object and morphism is isomorph
ic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : CochainComplex V ℕ) :
    augment (truncate.obj C) (C.d 0 1) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;> aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> rcases i with - | i <;> aesop }

@[simp]
/-
**CochainComplex.augmentTruncate_hom_f_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex`。
形式化陈述：augmentTruncate_hom_f_zero (C : CochainComplex V Nat) : (augmentTruncate C
).hom.f 0 = 𝟙 (C.X 0)
参数：C : CochainComplex V Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_hom_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/-
**CochainComplex.augmentTruncate_hom_f_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex`。
形式化陈述：augmentTruncate_hom_f_succ (C : CochainComplex V Nat) (i : Nat) : (augment
Truncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1))
参数：C : CochainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_hom_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
/-
**CochainComplex.augmentTruncate_inv_f_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex`。
形式化陈述：augmentTruncate_inv_f_zero (C : CochainComplex V Nat) : (augmentTruncate C
).inv.f 0 = 𝟙 (C.X 0)
参数：C : CochainComplex V Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_inv_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/-
**CochainComplex.augmentTruncate_inv_f_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex`。
形式化陈述：augmentTruncate_inv_f_succ (C : CochainComplex V Nat) (i : Nat) : (augment
Truncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1))
参数：C : CochainComplex V Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem augmentTruncate_inv_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a single object cochain complex in degree zero to a cochain complex
can be reinterpreted as a cochain complex.

This is the inverse construction of `toTruncate`.
-/
/-
**CochainComplex.fromSingle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain map from a single object cochain complex in degree zero to a cochain com
plex
can be reinterpreted as a cochain complex.

This is the inverse construction of `toTruncate`.
-/
def fromSingle₀AsComplex [HasZeroObject V] (C : CochainComplex V ℕ) (X : V)
    (f : (single₀ V).obj X ⟶ C) : CochainComplex V ℕ :=
  let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

end CochainComplex

