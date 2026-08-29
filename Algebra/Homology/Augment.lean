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
/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: [HasZeroMorphisms V]
  body: { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
shape := fun i j w => C.shape _ _ by simpa }
  map f := { f := fun i => f.f (i + 1) }

中文:
定义 truncate
  签名: [HasZeroMorphisms V]
  定义体: { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
shape := fun i j w => C.shape _ _ by simpa }
  map f := { f := fun i => f.f (i + 1) }

Depends on / 依赖: C.shape
-/
def truncate [HasZeroMorphisms V] : ChainComplex V Nat ⥤ ChainComplex V Nat where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
shape := fun i j w => C.shape _ _ by simpa }
  map f := { f := fun i => f.f (i + 1) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `truncateTo` / `truncateTo` 的定义

English:
definition truncateTo
  signature: [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V Nat)
  body: (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by simp⟩

中文:
定义 truncateTo
  签名: [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V 自然数)
  定义体: (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by simp⟩

Depends on / 依赖: truncate, truncate.obj
-/
def truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V Nat) :
    truncate.obj C ⟶ (single₀ V).obj (C.X 0) :=
  (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by simp⟩

-- PROJECT when `V` is abelian (but not generally?)
-- `[∀ n, Exact (C.d (n+2) (n+1)) (C.d (n+1) n)] [Epi (C.d 1 0)]` iff `QuasiIso (C.truncate_to)`
variable [HasZeroMorphisms V]

/--
Definition of `augment` / `augment` 的定义

English:
definition augment
  signature: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)

中文:
定义 augment
  签名: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
-/
def augment (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    ChainComplex V Nat where
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
/--
theorem `augment_X_zero` / 定理 `augment_X_zero`

English:
theorem augment_X_zero
  given: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: rfl

@[simp]

中文:
定理 augment_X_zero
  条件: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: rfl

@[simp]
-/
theorem augment_X_zero (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
/--
theorem `augment_X_succ` / 定理 `augment_X_succ`

English:
theorem augment_X_succ
  statement: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: rfl

@[simp]

中文:
定理 augment_X_succ
  结论: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: rfl

@[simp]
-/
theorem augment_X_succ (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : Nat) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
/--
theorem `augment_d_one_zero` / 定理 `augment_d_one_zero`

English:
theorem augment_d_one_zero
  given: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: rfl

@[simp]

中文:
定理 augment_d_one_zero
  条件: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: rfl

@[simp]
-/
theorem augment_d_one_zero (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).d 1 0 = f :=
  rfl

@[simp]
/--
theorem `augment_d_succ_succ` / 定理 `augment_d_succ_succ`

English:
theorem augment_d_succ_succ
  statement: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: by
  cases i <;> rfl

中文:
定理 augment_d_succ_succ
  结论: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: by
  cases i <;> rfl
-/
theorem augment_d_succ_succ (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i j : Nat) : (augment C f w).d (i + 1) (j + 1) = C.d i j := by
  cases i <;> rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `truncateAugment` / `truncateAugment` 的定义

English:
definition truncateAugment
  signature: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  body: { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext (_ | i) <;> simp
  inv_hom_id := by
    ext (_ | i) <;> simp

@[simp]

中文:
定义 truncateAugment
  签名: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  定义体: { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext (_ | i) <;> simp
  inv_hom_id := by
    ext (_ | i) <;> simp

@[simp]
-/
def truncateAugment (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
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
/--
theorem `truncateAugment_hom_f` / 定理 `truncateAugment_hom_f`

English:
theorem truncateAugment_hom_f
  statement: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: rfl

@[simp]

中文:
定理 truncateAugment_hom_f
  结论: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: rfl

@[simp]
-/
theorem truncateAugment_hom_f (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : Nat) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
/--
theorem `truncateAugment_inv_f` / 定理 `truncateAugment_inv_f`

English:
theorem truncateAugment_inv_f
  statement: (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  proof: rfl

@[simp]

中文:
定理 truncateAugment_inv_f
  结论: (C : ChainComplex V 自然数) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  证明: rfl

@[simp]
-/
theorem truncateAugment_inv_f (C : ChainComplex V Nat) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : Nat) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
/--
theorem `chainComplex_d_succ_succ_zero` / 定理 `chainComplex_d_succ_succ_zero`

English:
theorem chainComplex_d_succ_succ_zero
  given: (C : ChainComplex V Nat) (i : Nat)
  statement: C.d (i + 2) 0 = 0
  proof: by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

中文:
定理 chainComplex_d_succ_succ_zero
  条件: (C : ChainComplex V 自然数) (i : 自然数)
  结论: C.d (i + 2) 0 = 0
  证明: by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

Depends on / 依赖: C.shape, i.succ_succ_ne_one.symm, succ_succ_ne_one
-/
theorem chainComplex_d_succ_succ_zero (C : ChainComplex V Nat) (i : Nat) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `augmentTruncate` / `augmentTruncate` 的定义

English:
definition augmentTruncate
  signature: (C : ChainComplex V Nat)
  body: { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
        | 0 | 1 | n + 2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
          |

中文:
定义 augmentTruncate
  签名: (C : ChainComplex V 自然数)
  定义体: { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
        | 0 | 1 | n + 2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        match i with
          |

Depends on / 依赖: augment, hom_inv_id, inv_hom_id, truncate
-/
def augmentTruncate (C : ChainComplex V Nat) :
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
/--
theorem `augmentTruncate_hom_f_zero` / 定理 `augmentTruncate_hom_f_zero`

English:
theorem augmentTruncate_hom_f_zero
  given: (C : ChainComplex V Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_hom_f_zero
  条件: (C : ChainComplex V 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_hom_f_zero (C : ChainComplex V Nat) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_hom_f_succ` / 定理 `augmentTruncate_hom_f_succ`

English:
theorem augmentTruncate_hom_f_succ
  given: (C : ChainComplex V Nat) (i : Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_hom_f_succ
  条件: (C : ChainComplex V 自然数) (i : 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_hom_f_succ (C : ChainComplex V Nat) (i : Nat) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_inv_f_zero` / 定理 `augmentTruncate_inv_f_zero`

English:
theorem augmentTruncate_inv_f_zero
  given: (C : ChainComplex V Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_inv_f_zero
  条件: (C : ChainComplex V 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_inv_f_zero (C : ChainComplex V Nat) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_inv_f_succ` / 定理 `augmentTruncate_inv_f_succ`

English:
theorem augmentTruncate_inv_f_succ
  given: (C : ChainComplex V Nat) (i : Nat)
  proof: rfl

中文:
定理 augmentTruncate_inv_f_succ
  条件: (C : ChainComplex V 自然数) (i : 自然数)
  证明: rfl
-/
theorem augmentTruncate_inv_f_succ (C : ChainComplex V Nat) (i : Nat) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/--
Definition of `toSingle₀AsComplex` / `toSingle₀AsComplex` 的定义

English:
definition toSingle₀AsComplex
  signature: [HasZeroObject V] (C : ChainComplex V Nat) (X : V)
  body: let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

中文:
定义 toSingle₀AsComplex
  签名: [HasZeroObject V] (C : ChainComplex V 自然数) (X : V)
  定义体: let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

Depends on / 依赖: augment
-/
def toSingle₀AsComplex [HasZeroObject V] (C : ChainComplex V Nat) (X : V)
    (f : C ⟶ (single₀ V).obj X) : ChainComplex V Nat :=
  let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

end ChainComplex

namespace CochainComplex

/-- The truncation of an `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: [HasZeroMorphisms V]
  body: { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

中文:
定义 truncate
  签名: [HasZeroMorphisms V]
  定义体: { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

Depends on / 依赖: C.shape
-/
def truncate [HasZeroMorphisms V] : CochainComplex V Nat ⥤ CochainComplex V Nat where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toTruncate` / `toTruncate` 的定义

English:
definition toTruncate
  signature: [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V Nat)
  body: (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by simp⟩

中文:
定义 toTruncate
  签名: [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V 自然数)
  定义体: (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by simp⟩

Depends on / 依赖: truncate, truncate.obj
-/
def toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V Nat) :
    (single₀ V).obj (C.X 0) ⟶ truncate.obj C :=
  (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by simp⟩

variable [HasZeroMorphisms V]

/--
Definition of `augment` / `augment` 的定义

English:
definition augment
  signature: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  body: by
    rcases j with (_ | _ | j) <;> cases i <;> simp_all
  d_comp_d' i j k hij hjk := by
    have (k : Nat) : f ≫ C.d 0 (k + 1) = 0 := by
      cases k
      · exact w
      · rw [C.shape, comp_zero]
        simp only [ComplexShape.up_Rel, zero_add]
        exact (Nat.one_lt_succ_succ _).ne
    rca

中文:
定义 augment
  签名: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  定义体: by
    rcases j with (_ | _ | j) <;> cases i <;> simp_all
  d_comp_d' i j k hij hjk := by
    have (k : Nat) : f ≫ C.d 0 (k + 1) = 0 := by
      cases k
      · exact w
      · rw [C.shape, comp_zero]
        simp only [ComplexShape.up_Rel, zero_add]
        exact (Nat.one_lt_succ_succ _).ne
    rca

Depends on / 依赖: C.shape, ComplexShape, ComplexShape.up_Rel, Nat.one_lt_succ_succ, comp_zero, d_comp_d, one_lt_succ_succ, up_Rel, zero_add
-/
def augment (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    CochainComplex V Nat where
  X | 0 => X
    | i + 1 => C.X i
  d | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape i j s := by
    rcases j with (_ | _ | j) <;> cases i <;> simp_all
  d_comp_d' i j k hij hjk := by
    have (k : Nat) : f ≫ C.d 0 (k + 1) = 0 := by
      cases k
      · exact w
      · rw [C.shape, comp_zero]
        simp only [ComplexShape.up_Rel, zero_add]
        exact (Nat.one_lt_succ_succ _).ne
    rcases k with (_ | _ | k) <;> rcases j with (_ | _ | j) <;> cases i <;> simp [this]

@[simp]
/--
theorem `augment_X_zero` / 定理 `augment_X_zero`

English:
theorem augment_X_zero
  given: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  proof: rfl

@[simp]

中文:
定理 augment_X_zero
  条件: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  证明: rfl

@[simp]
-/
theorem augment_X_zero (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
/--
theorem `augment_X_succ` / 定理 `augment_X_succ`

English:
theorem augment_X_succ
  statement: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  proof: rfl

@[simp]

中文:
定理 augment_X_succ
  结论: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  证明: rfl

@[simp]
-/
theorem augment_X_succ (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i : Nat) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
/--
theorem `augment_d_zero_one` / 定理 `augment_d_zero_one`

English:
theorem augment_d_zero_one
  given: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  proof: rfl

@[simp]

中文:
定理 augment_d_zero_one
  条件: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  证明: rfl

@[simp]
-/
theorem augment_d_zero_one (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).d 0 1 = f :=
  rfl

@[simp]
/--
theorem `augment_d_succ_succ` / 定理 `augment_d_succ_succ`

English:
theorem augment_d_succ_succ
  statement: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  proof: rfl

中文:
定理 augment_d_succ_succ
  结论: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  证明: rfl
-/
theorem augment_d_succ_succ (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i j : Nat) : (augment C f w).d (i + 1) (j + 1) = C.d i j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `truncateAugment` / `truncateAugment` 的定义

English:
definition truncateAugment
  signature: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  body: { f := fun _ => 𝟙 _ }
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

中文:
定义 truncateAugment
  签名: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
  定义体: { f := fun _ => 𝟙 _ }
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
-/
def truncateAugment (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
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
/--
theorem `truncateAugment_hom_f` / 定理 `truncateAugment_hom_f`

English:
theorem truncateAugment_hom_f
  statement: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0)
  proof: rfl

@[simp]

中文:
定理 truncateAugment_hom_f
  结论: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0)
  证明: rfl

@[simp]
-/
theorem truncateAugment_hom_f (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : Nat) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
/--
theorem `truncateAugment_inv_f` / 定理 `truncateAugment_inv_f`

English:
theorem truncateAugment_inv_f
  statement: (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0)
  proof: rfl

@[simp]

中文:
定理 truncateAugment_inv_f
  结论: (C : CochainComplex V 自然数) {X : V} (f : X ⟶ C.X 0)
  证明: rfl

@[simp]
-/
theorem truncateAugment_inv_f (C : CochainComplex V Nat) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : Nat) :
    (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
/--
theorem `cochainComplex_d_succ_succ_zero` / 定理 `cochainComplex_d_succ_succ_zero`

English:
theorem cochainComplex_d_succ_succ_zero
  given: (C : CochainComplex V Nat) (i : Nat)
  statement: C.d 0 (i + 2) = 0
  proof: by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

中文:
定理 cochainComplex_d_succ_succ_zero
  条件: (C : CochainComplex V 自然数) (i : 自然数)
  结论: C.d 0 (i + 2) = 0
  证明: by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

Depends on / 依赖: C.shape, ComplexShape, ComplexShape.up_Rel, Nat.one_lt_succ_succ, one_lt_succ_succ, up_Rel, zero_add
-/
theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V Nat) (i : Nat) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `augmentTruncate` / `augmentTruncate` 的定义

English:
definition augmentTruncate
  signature: (C : CochainComplex V Nat)
  body: { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;> aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> rcases i with - | i <;> aesop }

@[simp]

中文:
定义 augmentTruncate
  签名: (C : CochainComplex V 自然数)
  定义体: { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;> aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> rcases i with - | i <;> aesop }

@[simp]
-/
def augmentTruncate (C : CochainComplex V Nat) :
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
/--
theorem `augmentTruncate_hom_f_zero` / 定理 `augmentTruncate_hom_f_zero`

English:
theorem augmentTruncate_hom_f_zero
  given: (C : CochainComplex V Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_hom_f_zero
  条件: (C : CochainComplex V 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_hom_f_zero (C : CochainComplex V Nat) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_hom_f_succ` / 定理 `augmentTruncate_hom_f_succ`

English:
theorem augmentTruncate_hom_f_succ
  given: (C : CochainComplex V Nat) (i : Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_hom_f_succ
  条件: (C : CochainComplex V 自然数) (i : 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_hom_f_succ (C : CochainComplex V Nat) (i : Nat) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_inv_f_zero` / 定理 `augmentTruncate_inv_f_zero`

English:
theorem augmentTruncate_inv_f_zero
  given: (C : CochainComplex V Nat)
  proof: rfl

@[simp]

中文:
定理 augmentTruncate_inv_f_zero
  条件: (C : CochainComplex V 自然数)
  证明: rfl

@[simp]
-/
theorem augmentTruncate_inv_f_zero (C : CochainComplex V Nat) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
/--
theorem `augmentTruncate_inv_f_succ` / 定理 `augmentTruncate_inv_f_succ`

English:
theorem augmentTruncate_inv_f_succ
  given: (C : CochainComplex V Nat) (i : Nat)
  proof: rfl

中文:
定理 augmentTruncate_inv_f_succ
  条件: (C : CochainComplex V 自然数) (i : 自然数)
  证明: rfl
-/
theorem augmentTruncate_inv_f_succ (C : CochainComplex V Nat) (i : Nat) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/--
Definition of `fromSingle₀AsComplex` / `fromSingle₀AsComplex` 的定义

English:
definition fromSingle₀AsComplex
  signature: [HasZeroObject V] (C : CochainComplex V Nat) (X : V)
  body: let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

中文:
定义 fromSingle₀AsComplex
  签名: [HasZeroObject V] (C : CochainComplex V 自然数) (X : V)
  定义体: let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

Depends on / 依赖: augment
-/
def fromSingle₀AsComplex [HasZeroObject V] (C : CochainComplex V Nat) (X : V)
    (f : (single₀ V).obj X ⟶ C) : CochainComplex V Nat :=
  let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

end CochainComplex
