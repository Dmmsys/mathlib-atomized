/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.Abel

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}
variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section

/--
Definition of `dNext` / `dNext` 的定义

English:
definition dNext
  signature: (i : ι)
  body: AddMonoidHom.mk' (fun f => C.d i (c.next i) ≫ f (c.next i) i) fun _ _ =>
    Preadditive.comp_add _ _ _ _ _ _

中文:
定义 dNext
  签名: (i : ι)
  定义体: AddMonoidHom.mk' (fun f => C.d i (c.next i) ≫ f (c.next i) i) fun _ _ =>
    Preadditive.comp_add _ _ _ _ _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, Preadditive, Preadditive.comp_add, c.next, comp_add
-/
def dNext (i : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => C.d i (c.next i) ≫ f (c.next i) i) fun _ _ =>
    Preadditive.comp_add _ _ _ _ _ _

/--
Definition of `fromNext` / `fromNext` 的定义

English:
definition fromNext
  signature: (i : ι)
  body: AddMonoidHom.mk' (fun f => f (c.next i) i) fun _ _ => rfl

@[simp]

中文:
定义 fromNext
  签名: (i : ι)
  定义体: AddMonoidHom.mk' (fun f => f (c.next i) i) fun _ _ => rfl

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, c.next
-/
def fromNext (i : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.xNext i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => f (c.next i) i) fun _ _ => rfl

@[simp]
/--
theorem `dNext_eq_dFrom_fromNext` / 定理 `dNext_eq_dFrom_fromNext`

English:
theorem dNext_eq_dFrom_fromNext
  given: (f : forall i j, C.X i ⟶ D.X j) (i : ι)
  proof: rfl

中文:
定理 dNext_eq_dFrom_fromNext
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (i : ι)
  证明: rfl
-/
theorem dNext_eq_dFrom_fromNext (f : forall i j, C.X i ⟶ D.X j) (i : ι) :
    dNext i f = C.dFrom i ≫ fromNext i f :=
  rfl

/--
theorem `dNext_eq` / 定理 `dNext_eq`

English:
theorem dNext_eq
  given: (f : forall i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel i i')
  proof: by
  obtain rfl := c.next_eq' w
  rfl

中文:
定理 dNext_eq
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.关系 i i')
  证明: by
  obtain rfl := c.next_eq' w
  rfl

Depends on / 依赖: c.next_eq, next_eq
-/
theorem dNext_eq (f : forall i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel i i') :
    dNext i f = C.d i i' ≫ f i' i := by
  obtain rfl := c.next_eq' w
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `dNext_eq_zero` / 引理 `dNext_eq_zero`

English:
lemma dNext_eq_zero
  given: (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel i (c.next i))
  proof: by
  dsimp [dNext]
  rw [shape _ _ _ hi]; rw [zero_comp]

中文:
引理 dNext_eq_zero
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.关系 i (c.next i))
  证明: by
  dsimp [dNext]
  rw [shape _ _ _ hi]; rw [zero_comp]

Depends on / 依赖: zero_comp
-/
lemma dNext_eq_zero (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    dNext i f = 0 := by
  dsimp [dNext]
  rw [shape _ _ _ hi]; rw [zero_comp]

-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dNext_comp_left` / 定理 `dNext_comp_left`

English:
theorem dNext_comp_left
  given: (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (i : ι)
  proof: (f.comm_assoc _ _ _).symm

中文:
定理 dNext_comp_left
  条件: (f : C ⟶ D) (g : 对任意 i j, D.X i ⟶ E.X j) (i : ι)
  证明: (f.comm_assoc _ _ _).symm

Depends on / 依赖: comm_assoc, f.comm_assoc
-/
theorem dNext_comp_left (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (i : ι) :
    (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g :=
  (f.comm_assoc _ _ _).symm

-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dNext_comp_right` / 定理 `dNext_comp_right`

English:
theorem dNext_comp_right
  given: (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι)
  proof: (assoc _ _ _).symm

中文:
定理 dNext_comp_right
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι)
  证明: (assoc _ _ _).symm
-/
theorem dNext_comp_right (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
    (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i :=
  (assoc _ _ _).symm

/--
Definition of `prevD` / `prevD` 的定义

English:
definition prevD
  signature: (j : ι)
  body: AddMonoidHom.mk' (fun f => f j (c.prev j) ≫ D.d (c.prev j) j) fun _ _ =>
    Preadditive.add_comp _ _ _ _ _ _

中文:
定义 prevD
  签名: (j : ι)
  定义体: AddMonoidHom.mk' (fun f => f j (c.prev j) ≫ D.d (c.prev j) j) fun _ _ =>
    Preadditive.add_comp _ _ _ _ _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, Preadditive, Preadditive.add_comp, add_comp, c.prev
-/
def prevD (j : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X j ⟶ D.X j) :=
  AddMonoidHom.mk' (fun f => f j (c.prev j) ≫ D.d (c.prev j) j) fun _ _ =>
    Preadditive.add_comp _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `prevD_eq_zero` / 引理 `prevD_eq_zero`

English:
lemma prevD_eq_zero
  given: (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel (c.prev i) i)
  proof: by
  dsimp [prevD]
  rw [shape _ _ _ hi]; rw [comp_zero]

中文:
引理 prevD_eq_zero
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.关系 (c.prev i) i)
  证明: by
  dsimp [prevD]
  rw [shape _ _ _ hi]; rw [comp_zero]

Depends on / 依赖: comp_zero
-/
lemma prevD_eq_zero (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel (c.prev i) i) :
    prevD i f = 0 := by
  dsimp [prevD]
  rw [shape _ _ _ hi]; rw [comp_zero]

/--
Definition of `toPrev` / `toPrev` 的定义

English:
definition toPrev
  signature: (j : ι)
  body: AddMonoidHom.mk' (fun f => f j (c.prev j)) fun _ _ => rfl

@[simp]

中文:
定义 toPrev
  签名: (j : ι)
  定义体: AddMonoidHom.mk' (fun f => f j (c.prev j)) fun _ _ => rfl

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, c.prev
-/
def toPrev (j : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X j ⟶ D.xPrev j) :=
  AddMonoidHom.mk' (fun f => f j (c.prev j)) fun _ _ => rfl

@[simp]
/--
theorem `prevD_eq_toPrev_dTo` / 定理 `prevD_eq_toPrev_dTo`

English:
theorem prevD_eq_toPrev_dTo
  given: (f : forall i j, C.X i ⟶ D.X j) (j : ι)
  proof: rfl

中文:
定理 prevD_eq_toPrev_dTo
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (j : ι)
  证明: rfl
-/
theorem prevD_eq_toPrev_dTo (f : forall i j, C.X i ⟶ D.X j) (j : ι) :
    prevD j f = toPrev j f ≫ D.dTo j :=
  rfl

/--
theorem `prevD_eq` / 定理 `prevD_eq`

English:
theorem prevD_eq
  given: (f : forall i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel j' j)
  proof: by
  obtain rfl := c.prev_eq' w
  rfl

中文:
定理 prevD_eq
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.关系 j' j)
  证明: by
  obtain rfl := c.prev_eq' w
  rfl

Depends on / 依赖: c.prev_eq, prev_eq
-/
theorem prevD_eq (f : forall i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel j' j) :
    prevD j f = f j j' ≫ D.d j' j := by
  obtain rfl := c.prev_eq' w
  rfl

-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `prevD_comp_left` / 定理 `prevD_comp_left`

English:
theorem prevD_comp_left
  given: (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (j : ι)
  proof: assoc _ _ _

中文:
定理 prevD_comp_left
  条件: (f : C ⟶ D) (g : 对任意 i j, D.X i ⟶ E.X j) (j : ι)
  证明: assoc _ _ _
-/
theorem prevD_comp_left (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (j : ι) :
    (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g :=
  assoc _ _ _

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `prevD_comp_right` / 定理 `prevD_comp_right`

English:
theorem prevD_comp_right
  given: (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι)
  proof: by
  dsimp [prevD]
  simp only [assoc, g.comm]

中文:
定理 prevD_comp_right
  条件: (f : 对任意 i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι)
  证明: by
  dsimp [prevD]
  simp only [assoc, g.comm]

Depends on / 依赖: g.comm
-/
theorem prevD_comp_right (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
    (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j := by
  dsimp [prevD]
  simp only [assoc, g.comm]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `dNext_nat` / 定理 `dNext_nat`

English:
theorem dNext_nat
  given: (C D : ChainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ D.X j)
  proof: by
  dsimp [dNext]
  cases i
  · simp
  · congr <;> simp

中文:
定理 dNext_nat
  条件: (C D : 链复形 V 自然数) (i : 自然数) (f : 对任意 i j, C.X i ⟶ D.X j)
  证明: by
  dsimp [dNext]
  cases i
  · simp
  · congr <;> simp
-/
theorem dNext_nat (C D : ChainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ D.X j) :
    dNext i f = C.d i (i - 1) ≫ f (i - 1) i := by
  dsimp [dNext]
  cases i
  · simp
  · congr <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `prevD_nat` / 定理 `prevD_nat`

English:
theorem prevD_nat
  given: (C D : CochainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ D.X j)
  proof: by
  dsimp [prevD]
  cases i
  · simp
  · congr <;> simp

中文:
定理 prevD_nat
  条件: (C D : 上链复形 V 自然数) (i : 自然数) (f : 对任意 i j, C.X i ⟶ D.X j)
  证明: by
  dsimp [prevD]
  cases i
  · simp
  · congr <;> simp
-/
theorem prevD_nat (C D : CochainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ D.X j) :
    prevD i f = f i (i - 1) ≫ D.d (i - 1) i := by
  dsimp [prevD]
  cases i
  · simp
  · congr <;> simp

/-- A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.Rel j i`, satisfying the homotopy condition.
-/
@[ext]
/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
structure Homotopy
  parameters: (f g : C ⟶ D)
  axioms and operations (3):
    - hom : forall i j, C.X i ⟶ D.X j
    - zero : forall i j, ¬c.Rel j i -> hom i j = 0  [default: by cat_disch]
    - comm : forall i, f.f i = dNext i hom + prevD i hom + g.f i  [default: by cat_disch]

中文:
结构 同伦
  参数: (f g : C ⟶ D)
  公理与运算 (3 个):
    - hom : 对任意 i j, C.X i ⟶ D.X j
    - zero : 对任意 i j, ¬c.关系 j i -> hom i j = 0  [默认: by cat_disch]
    - comm : 对任意 i, f.f i = dNext i hom + prevD i hom + g.f i  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Homotopy (f g : C ⟶ D) where
  hom : forall i j, C.X i ⟶ D.X j
  zero : forall i j, ¬c.Rel j i -> hom i j = 0 := by cat_disch
  comm : forall i, f.f i = dNext i hom + prevD i hom + g.f i := by cat_disch

variable {f g}

namespace Homotopy

/--
Definition of `equivSubZero` / `equivSubZero` 的定义

English:
definition equivSubZero
  signature: : Homotopy f g ≃ Homotopy (f - g) 0 where
  body: { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simp [h.comm] }
  invFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simpa [sub_eq_iff_eq_add] using h.comm i }
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 equivSubZero
  签名: : 同伦 f g ≃ 同伦 (f - g) 0 where
  定义体: { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simp [h.comm] }
  invFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simpa [sub_eq_iff_eq_add] using h.comm i }
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: cat_disch, h.comm, h.hom, h.zero, invFun, left_inv, right_inv, sub_eq_iff_eq_add
-/
def equivSubZero : Homotopy f g ≃ Homotopy (f - g) 0 where
  toFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simp [h.comm] }
  invFun h :=
    { hom := fun i j => h.hom i j
      zero := fun _ _ w => h.zero _ _ w
      comm := fun i => by simpa [sub_eq_iff_eq_add] using h.comm i }
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal chain maps are homotopic. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : f = g)
  body: 0
  zero _ _ _ := rfl

中文:
定义 ofEq
  签名: (h : f = g)
  定义体: 0
  zero _ _ _ := rfl
-/
def ofEq (h : f = g) : Homotopy f g where
  hom := 0
  zero _ _ _ := rfl

/-- Every chain map is homotopic to itself. -/
@[simps!, refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : C ⟶ D)
  body: ofEq (rfl : f = f)

中文:
定义 refl
  签名: (f : C ⟶ D)
  定义体: ofEq (rfl : f = f)
-/
def refl (f : C ⟶ D) : Homotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps!, symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f g : C ⟶ D} (h : Homotopy f g)
  body: -h.hom
  zero i j w := by rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm i := by
    rw [map_neg]; rw [map_neg]; rw [h.comm]; rw [← neg_add]; rw [← add_assoc]; rw [neg_add_cancel]; rw [zero_add]

中文:
定义 symm
  签名: {f g : C ⟶ D} (h : 同伦 f g)
  定义体: -h.hom
  zero i j w := by rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm i := by
    rw [map_neg]; rw [map_neg]; rw [h.comm]; rw [← neg_add]; rw [← add_assoc]; rw [neg_add_cancel]; rw [zero_add]

Depends on / 依赖: h.hom
-/
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where
  hom := -h.hom
  zero i j w := by rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm i := by
    rw [map_neg]; rw [map_neg]; rw [h.comm]; rw [← neg_add]; rw [← add_assoc]; rw [neg_add_cancel]; rw [zero_add]

/-- homotopy is a transitive relation. -/
@[simps!, trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g)
  body: h.hom + k.hom
  zero i j w := by rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_add]
  comm i := by grind [Homotopy.comm]

中文:
定义 trans
  签名: {e f g : C ⟶ D} (h : 同伦 e f) (k : 同伦 f g)
  定义体: h.hom + k.hom
  zero i j w := by rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_add]
  comm i := by grind [Homotopy.comm]

Depends on / 依赖: h.hom, k.hom
-/
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g where
  hom := h.hom + k.hom
  zero i j w := by rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_add]
  comm i := by grind [Homotopy.comm]

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps!]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂)
  body: h₁.hom + h₂.hom
  zero i j hij := by rw [Pi.add_apply, Pi.add_apply, h₁.zero i j hij, h₂.zero i j hij, add_zero]
  comm i := by grind [HomologicalComplex.add_f_apply, Homotopy.comm]

中文:
定义 add
  签名: {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : 同伦 f₁ g₁) (h₂ : 同伦 f₂ g₂)
  定义体: h₁.hom + h₂.hom
  zero i j hij := by rw [Pi.add_apply, Pi.add_apply, h₁.zero i j hij, h₂.zero i j hij, add_zero]
  comm i := by grind [HomologicalComplex.add_f_apply, Homotopy.comm]
-/
def add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  zero i j hij := by rw [Pi.add_apply, Pi.add_apply, h₁.zero i j hij, h₂.zero i j hij, add_zero]
  comm i := by grind [HomologicalComplex.add_f_apply, Homotopy.comm]

set_option backward.defeqAttrib.useBackward true in
/-- the scalar multiplication of a homotopy -/
@[simps!]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R)
  body: a • h.hom i j
  zero i j hij := by
    rw [h.zero i j hij]; rw [smul_zero]
  comm i := by
    dsimp
    rw [h.comm]
    dsimp [fromNext, toPrev]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]

中文:
定义 smul
  签名: {R : 类型} [半环 R] [线性 R V] (h : 同伦 f g) (a : R)
  定义体: a • h.hom i j
  zero i j hij := by
    rw [h.zero i j hij]; rw [smul_zero]
  comm i := by
    dsimp
    rw [h.comm]
    dsimp [fromNext, toPrev]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]

Depends on / 依赖: h.hom
-/
def smul {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R) :
    Homotopy (a • f) (a • g) where
  hom i j := a • h.hom i j
  zero i j hij := by
    rw [h.zero i j hij]; rw [smul_zero]
  comm i := by
    dsimp
    rw [h.comm]
    dsimp [fromNext, toPrev]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]

/-- homotopy is closed under composition (on the right) -/
@[simps]
/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E)
  body: h.hom i j ≫ g.f j
  zero i j w := by rw [h.zero i j w, zero_comp]
  comm i := by rw [comp_f, h.comm i, dNext_comp_right, prevD_comp_right, Preadditive.add_comp,
    comp_f, Preadditive.add_comp]

中文:
定义 compRight
  签名: {e f : C ⟶ D} (h : 同伦 e f) (g : D ⟶ E)
  定义体: h.hom i j ≫ g.f j
  zero i j w := by rw [h.zero i j w, zero_comp]
  comm i := by rw [comp_f, h.comm i, dNext_comp_right, prevD_comp_right, Preadditive.add_comp,
    comp_f, Preadditive.add_comp]

Depends on / 依赖: h.hom
-/
def compRight {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) where
  hom i j := h.hom i j ≫ g.f j
  zero i j w := by rw [h.zero i j w, zero_comp]
  comm i := by rw [comp_f, h.comm i, dNext_comp_right, prevD_comp_right, Preadditive.add_comp,
    comp_f, Preadditive.add_comp]

/-- homotopy is closed under composition (on the left) -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D)
  body: e.f i ≫ h.hom i j
  zero i j w := by rw [h.zero i j w, comp_zero]
  comm i := by rw [comp_f, h.comm i, dNext_comp_left, prevD_comp_left, comp_f,
    Preadditive.comp_add, Preadditive.comp_add]

中文:
定义 compLeft
  签名: {f g : D ⟶ E} (h : 同伦 f g) (e : C ⟶ D)
  定义体: e.f i ≫ h.hom i j
  zero i j w := by rw [h.zero i j w, comp_zero]
  comm i := by rw [comp_f, h.comm i, dNext_comp_left, prevD_comp_left, comp_f,
    Preadditive.comp_add, Preadditive.comp_add]

Depends on / 依赖: h.hom
-/
def compLeft {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) where
  hom i j := e.f i ≫ h.hom i j
  zero i j w := by rw [h.zero i j w, comp_zero]
  comm i := by rw [comp_f, h.comm i, dNext_comp_left, prevD_comp_left, comp_f,
    Preadditive.comp_add, Preadditive.comp_add]

/-- homotopy is closed under composition -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
  body: (h₁.compRight _).trans (h₂.compLeft _)

中文:
定义 comp
  签名: {C₁ C₂ C₃ : 同调复形 V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
  定义体: (h₁.compRight _).trans (h₂.compLeft _)

Depends on / 依赖: compLeft, compRight
-/
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
    (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `Homotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compRightId` / `compRightId` 的定义

English:
definition compRightId
  signature: {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D)
  body: (h.compRight g).trans (ofEq <| id_comp _)

中文:
定义 compRightId
  签名: {f : C ⟶ C} (h : 同伦 f (𝟙 C)) (g : C ⟶ D)
  定义体: (h.compRight g).trans (ofEq <| id_comp _)

Depends on / 依赖: compRight, h.compRight, id_comp
-/
def compRightId {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- a variant of `Homotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compLeftId` / `compLeftId` 的定义

English:
definition compLeftId
  signature: {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D)
  body: (h.compLeft g).trans (ofEq <| comp_id _)

中文:
定义 compLeftId
  签名: {f : D ⟶ D} (h : 同伦 f (𝟙 D)) (g : C ⟶ D)
  定义体: (h.compLeft g).trans (ofEq <| comp_id _)

Depends on / 依赖: compLeft, comp_id, h.compLeft
-/
def compLeftId {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

/-!
Null homotopic maps can be constructed using the formula `hd+dh`. We show that
these morphisms are homotopic to `0` and provide some convenient simplification
lemmas that give a degreewise description of `hd+dh`, depending on whether we have
two differentials going to and from a certain degree, only one, or none.
-/


/--
Definition of `nullHomotopicMap` / `nullHomotopicMap` 的定义

English:
definition nullHomotopicMap
  signature: (hom : forall i j, C.X i ⟶ D.X j)
  body: dNext i hom + prevD i hom
  comm' i j hij := by
    have eq1 : prevD i hom ≫ D.d i j = 0 := by
      simp only [prevD, AddMonoidHom.mk'_apply, assoc, d_comp_d, comp_zero]
    have eq2 : C.d i j ≫ dNext j hom = 0 := by
      simp only [dNext, AddMonoidHom.mk'_apply, d_comp_d_assoc, zero_comp]
    rw [dNext_eq hom hij]; rw [prevD_eq hom hij]; rw [Preadditive.comp_add]; rw [Preadditive.add_comp]; rw [eq1]; rw [eq2]; rw [add_zero]; rw [zero_add]; rw [assoc]

中文:
定义 nullHomotopicMap
  签名: (hom : 对任意 i j, C.X i ⟶ D.X j)
  定义体: dNext i hom + prevD i hom
  comm' i j hij := by
    have eq1 : prevD i hom ≫ D.d i j = 0 := by
      simp only [prevD, AddMonoidHom.mk'_apply, assoc, d_comp_d, comp_zero]
    have eq2 : C.d i j ≫ dNext j hom = 0 := by
      simp only [dNext, AddMonoidHom.mk'_apply, d_comp_d_assoc, zero_comp]
    rw [dNext_eq hom hij]; rw [prevD_eq hom hij]; rw [Preadditive.comp_add]; rw [Preadditive.add_comp]; rw [eq1]; rw [eq2]; rw [add_zero]; rw [zero_add]; rw [assoc]
-/
def nullHomotopicMap (hom : forall i j, C.X i ⟶ D.X j) : C ⟶ D where
  f i := dNext i hom + prevD i hom
  comm' i j hij := by
    have eq1 : prevD i hom ≫ D.d i j = 0 := by
      simp only [prevD, AddMonoidHom.mk'_apply, assoc, d_comp_d, comp_zero]
    have eq2 : C.d i j ≫ dNext j hom = 0 := by
      simp only [dNext, AddMonoidHom.mk'_apply, d_comp_d_assoc, zero_comp]
    rw [dNext_eq hom hij]; rw [prevD_eq hom hij]; rw [Preadditive.comp_add]; rw [Preadditive.add_comp]; rw [eq1]; rw [eq2]; rw [add_zero]; rw [zero_add]; rw [assoc]

open scoped Classical in
/--
Definition of `nullHomotopicMap'` / `nullHomotopicMap'` 的定义

English:
definition nullHomotopicMap'
  signature: (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j))
  body: nullHomotopicMap fun i j => dite (c.Rel j i) (h i j) fun _ => 0

中文:
定义 nullHomotopicMap'
  签名: (h : 对任意 i j, c.关系 j i -> (C.X i ⟶ D.X j))
  定义体: nullHomotopicMap fun i j => dite (c.Rel j i) (h i j) fun _ => 0

Depends on / 依赖: c.Rel, nullHomotopicMap
-/
def nullHomotopicMap' (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) : C ⟶ D :=
  nullHomotopicMap fun i j => dite (c.Rel j i) (h i j) fun _ => 0

set_option backward.defeqAttrib.useBackward true in
/--
theorem `nullHomotopicMap_comp` / 定理 `nullHomotopicMap_comp`

English:
theorem nullHomotopicMap_comp
  given: (hom : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E)
  proof: by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.add_comp, assoc, g.comm]

中文:
定理 nullHomotopicMap_comp
  条件: (hom : 对任意 i j, C.X i ⟶ D.X j) (g : D ⟶ E)
  证明: by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.add_comp, assoc, g.comm]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, Preadditive, Preadditive.add_comp, _apply, add_comp, fromNext, g.comm, nullHomotopicMap, toPrev
-/
theorem nullHomotopicMap_comp (hom : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) :
    nullHomotopicMap hom ≫ g = nullHomotopicMap fun i j => hom i j ≫ g.f j := by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.add_comp, assoc, g.comm]

/--
theorem `nullHomotopicMap'_comp` / 定理 `nullHomotopicMap'_comp`

English:
theorem nullHomotopicMap'_comp
  given: (hom : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) (g : D ⟶ E)
  proof: by
  rw [nullHomotopicMap']; rw [nullHomotopicMap_comp]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [zero_comp]

中文:
定理 nullHomotopicMap'_comp
  条件: (hom : 对任意 i j, c.关系 j i -> (C.X i ⟶ D.X j)) (g : D ⟶ E)
  证明: by
  rw [nullHomotopicMap']; rw [nullHomotopicMap_comp]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [zero_comp]
-/
theorem nullHomotopicMap'_comp (hom : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) (g : D ⟶ E) :
    nullHomotopicMap' hom ≫ g = nullHomotopicMap' fun i j hij => hom i j hij ≫ g.f j := by
  rw [nullHomotopicMap']; rw [nullHomotopicMap_comp]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [zero_comp]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `comp_nullHomotopicMap` / 定理 `comp_nullHomotopicMap`

English:
theorem comp_nullHomotopicMap
  given: (f : C ⟶ D) (hom : forall i j, D.X i ⟶ E.X j)
  proof: by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.comp_add, assoc, f.comm_assoc]

中文:
定理 comp_nullHomotopicMap
  条件: (f : C ⟶ D) (hom : 对任意 i j, D.X i ⟶ E.X j)
  证明: by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.comp_add, assoc, f.comm_assoc]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, Preadditive, Preadditive.comp_add, _apply, comm_assoc, comp_add, f.comm_assoc, fromNext, nullHomotopicMap, toPrev
-/
theorem comp_nullHomotopicMap (f : C ⟶ D) (hom : forall i j, D.X i ⟶ E.X j) :
    f ≫ nullHomotopicMap hom = nullHomotopicMap fun i j => f.f i ≫ hom i j := by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.comp_add, assoc, f.comm_assoc]

/--
theorem `comp_nullHomotopicMap'` / 定理 `comp_nullHomotopicMap'`

English:
theorem comp_nullHomotopicMap'
  given: (f : C ⟶ D) (hom : forall i j, c.Rel j i -> (D.X i ⟶ E.X j))
  proof: by
  rw [nullHomotopicMap']; rw [comp_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [comp_zero]

中文:
定理 comp_nullHomotopicMap'
  条件: (f : C ⟶ D) (hom : 对任意 i j, c.关系 j i -> (D.X i ⟶ E.X j))
  证明: by
  rw [nullHomotopicMap']; rw [comp_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [comp_zero]

Depends on / 依赖: comp_nullHomotopicMap, comp_zero, nullHomotopicMap, split_ifs
-/
theorem comp_nullHomotopicMap' (f : C ⟶ D) (hom : forall i j, c.Rel j i -> (D.X i ⟶ E.X j)) :
    f ≫ nullHomotopicMap' hom = nullHomotopicMap' fun i j hij => f.f i ≫ hom i j hij := by
  rw [nullHomotopicMap']; rw [comp_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_nullHomotopicMap` / 定理 `map_nullHomotopicMap`

English:
theorem map_nullHomotopicMap
  statement: {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
  proof: by
  ext i
  dsimp [nullHomotopicMap, dNext, prevD]
  simp only [G.map_comp, Functor.map_add]

中文:
定理 map_nullHomotopicMap
  结论: {W : 类型} [范畴* W] [预加性 W] (G : V ⥤ W) [G.加性]
  证明: by
  ext i
  dsimp [nullHomotopicMap, dNext, prevD]
  simp only [G.map_comp, Functor.map_add]

Depends on / 依赖: Functor, Functor.map_add, G.map_comp, map_add, map_comp, nullHomotopicMap
-/
theorem map_nullHomotopicMap {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : forall i j, C.X i ⟶ D.X j) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap hom) =
      nullHomotopicMap (fun i j => by exact G.map (hom i j)) := by
  ext i
  dsimp [nullHomotopicMap, dNext, prevD]
  simp only [G.map_comp, Functor.map_add]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_nullHomotopicMap'` / 定理 `map_nullHomotopicMap'`

English:
theorem map_nullHomotopicMap'
  statement: {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
  proof: by
  rw [nullHomotopicMap']; rw [map_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [G.map_zero]

中文:
定理 map_nullHomotopicMap'
  结论: {W : 类型} [范畴* W] [预加性 W] (G : V ⥤ W) [G.加性]
  证明: by
  rw [nullHomotopicMap']; rw [map_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [G.map_zero]

Depends on / 依赖: G.map_zero, map_nullHomotopicMap, map_zero, nullHomotopicMap, split_ifs
-/
theorem map_nullHomotopicMap' {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap' hom) =
      nullHomotopicMap' fun i j hij => by exact G.map (hom i j hij) := by
  rw [nullHomotopicMap']; rw [map_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [G.map_zero]

/-- Tautological construction of the `Homotopy` to zero for maps constructed by
`nullHomotopicMap`, at least when we have the `zero` condition. -/
@[simps]
/--
Definition of `nullHomotopy` / `nullHomotopy` 的定义

English:
definition nullHomotopy
  signature: (hom : forall i j, C.X i ⟶ D.X j) (zero : forall i j, ¬c.Rel j i -> hom i j = 0)
  body: { hom := hom
    zero := zero
    comm := by
      intro i
      rw [HomologicalComplex.zero_f_apply]; rw [add_zero]
      rfl }

中文:
定义 nullHomotopy
  签名: (hom : 对任意 i j, C.X i ⟶ D.X j) (zero : 对任意 i j, ¬c.关系 j i -> hom i j = 0)
  定义体: { hom := hom
    zero := zero
    comm := by
      intro i
      rw [HomologicalComplex.zero_f_apply]; rw [add_zero]
      rfl }

Depends on / 依赖: HomologicalComplex, HomologicalComplex.zero_f_apply, add_zero, zero_f_apply
-/
def nullHomotopy (hom : forall i j, C.X i ⟶ D.X j) (zero : forall i j, ¬c.Rel j i -> hom i j = 0) :
    Homotopy (nullHomotopicMap hom) 0 :=
  { hom := hom
    zero := zero
    comm := by
      intro i
      rw [HomologicalComplex.zero_f_apply]; rw [add_zero]
      rfl }

open scoped Classical in
/-- Homotopy to zero for maps constructed with `nullHomotopicMap'` -/
@[simps!]
/--
Definition of `nullHomotopy'` / `nullHomotopy'` 的定义

English:
definition nullHomotopy'
  signature: (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j))
  body: by
  apply nullHomotopy fun i j => dite (c.Rel j i) (h i j) fun _ => 0
  grind

中文:
定义 nullHomotopy'
  签名: (h : 对任意 i j, c.关系 j i -> (C.X i ⟶ D.X j))
  定义体: by
  apply nullHomotopy fun i j => dite (c.Rel j i) (h i j) fun _ => 0
  grind

Depends on / 依赖: c.Rel, nullHomotopy
-/
def nullHomotopy' (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) : Homotopy (nullHomotopicMap' h) 0 := by
  apply nullHomotopy fun i j => dite (c.Rel j i) (h i j) fun _ => 0
  grind



-- Cannot be @[simp] because `k₀` and `k₂` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap_f` / 定理 `nullHomotopicMap_f`

English:
theorem nullHomotopicMap_f
  statement: {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
  proof: by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD_eq hom r₂₁]

中文:
定理 nullHomotopicMap_f
  结论: {k₂ k₁ k₀ : ι} (r₂₁ : c.关系 k₂ k₁) (r₁₀ : c.关系 k₁ k₀)
  证明: by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD_eq hom r₂₁]

Depends on / 依赖: dNext_eq, nullHomotopicMap, prevD_eq
-/
theorem nullHomotopicMap_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (hom : forall i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ := by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD_eq hom r₂₁]

-- Cannot be @[simp] because `k₀` and `k₂` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap'_f` / 定理 `nullHomotopicMap'_f`

English:
theorem nullHomotopicMap'_f
  statement: {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
  proof: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f r₂₁ r₁₀]
  split_ifs
  rfl

中文:
定理 nullHomotopicMap'_f
  结论: {k₂ k₁ k₀ : ι} (r₂₁ : c.关系 k₂ k₁) (r₁₀ : c.关系 k₁ k₀)
  证明: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f r₂₁ r₁₀]
  split_ifs
  rfl
-/
theorem nullHomotopicMap'_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ + h k₁ k₂ r₂₁ ≫ D.d k₂ k₁ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f r₂₁ r₁₀]
  split_ifs
  rfl

-- Cannot be @[simp] because `k₁` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap_f_of_not_rel_left` / 定理 `nullHomotopicMap_f_of_not_rel_left`

English:
theorem nullHomotopicMap_f_of_not_rel_left
  statement: {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
  proof: by
  dsimp only [nullHomotopicMap]
  rw [prevD_eq hom r₁₀]; rw [dNext]; rw [AddMonoidHom.mk'_apply]; rw [C.shape]; rw [zero_comp]; rw [zero_add]
  exact hk₀ _

中文:
定理 nullHomotopicMap_f_of_not_rel_left
  结论: {k₁ k₀ : ι} (r₁₀ : c.关系 k₁ k₀)
  证明: by
  dsimp only [nullHomotopicMap]
  rw [prevD_eq hom r₁₀]; rw [dNext]; rw [AddMonoidHom.mk'_apply]; rw [C.shape]; rw [zero_comp]; rw [zero_add]
  exact hk₀ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, C.shape, _apply, nullHomotopicMap, prevD_eq, zero_add, zero_comp
-/
theorem nullHomotopicMap_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : forall l : ι, ¬c.Rel k₀ l) (hom : forall i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ := by
  dsimp only [nullHomotopicMap]
  rw [prevD_eq hom r₁₀]; rw [dNext]; rw [AddMonoidHom.mk'_apply]; rw [C.shape]; rw [zero_comp]; rw [zero_add]
  exact hk₀ _

-- Cannot be @[simp] because `k₁` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap'_f_of_not_rel_left` / 定理 `nullHomotopicMap'_f_of_not_rel_left`

English:
theorem nullHomotopicMap'_f_of_not_rel_left
  statement: {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
  proof: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_left r₁₀ hk₀]
  split_ifs
  rfl

中文:
定理 nullHomotopicMap'_f_of_not_rel_left
  结论: {k₁ k₀ : ι} (r₁₀ : c.关系 k₁ k₀)
  证明: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_left r₁₀ hk₀]
  split_ifs
  rfl
-/
theorem nullHomotopicMap'_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : forall l : ι, ¬c.Rel k₀ l) (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_left r₁₀ hk₀]
  split_ifs
  rfl

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap_f_of_not_rel_right` / 定理 `nullHomotopicMap_f_of_not_rel_right`

English:
theorem nullHomotopicMap_f_of_not_rel_right
  statement: {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
  proof: by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD]; rw [AddMonoidHom.mk'_apply]; rw [D.shape]; rw [comp_zero]; rw [add_zero]
  exact hk₁ _

中文:
定理 nullHomotopicMap_f_of_not_rel_right
  结论: {k₁ k₀ : ι} (r₁₀ : c.关系 k₁ k₀)
  证明: by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD]; rw [AddMonoidHom.mk'_apply]; rw [D.shape]; rw [comp_zero]; rw [add_zero]
  exact hk₁ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, D.shape, _apply, add_zero, comp_zero, dNext_eq, nullHomotopicMap
-/
theorem nullHomotopicMap_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : forall l : ι, ¬c.Rel l k₁) (hom : forall i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ := by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀]; rw [prevD]; rw [AddMonoidHom.mk'_apply]; rw [D.shape]; rw [comp_zero]; rw [add_zero]
  exact hk₁ _

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.
/--
theorem `nullHomotopicMap'_f_of_not_rel_right` / 定理 `nullHomotopicMap'_f_of_not_rel_right`

English:
theorem nullHomotopicMap'_f_of_not_rel_right
  statement: {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
  proof: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_right r₁₀ hk₁]
  split_ifs
  rfl

中文:
定理 nullHomotopicMap'_f_of_not_rel_right
  结论: {k₁ k₀ : ι} (r₁₀ : c.关系 k₁ k₀)
  证明: by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_right r₁₀ hk₁]
  split_ifs
  rfl
-/
theorem nullHomotopicMap'_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : forall l : ι, ¬c.Rel l k₁) (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_right r₁₀ hk₁]
  split_ifs
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `nullHomotopicMap_f_eq_zero` / 定理 `nullHomotopicMap_f_eq_zero`

English:
theorem nullHomotopicMap_f_eq_zero
  statement: {k₀ : ι} (hk₀ : forall l : ι, ¬c.Rel k₀ l)
  proof: by
  dsimp [nullHomotopicMap, dNext, prevD]
  rw [C.shape]; rw [D.shape]; rw [zero_comp]; rw [comp_zero]; rw [add_zero] <;> apply_assumption

@[simp]

中文:
定理 nullHomotopicMap_f_eq_zero
  结论: {k₀ : ι} (hk₀ : 对任意 l : ι, ¬c.关系 k₀ l)
  证明: by
  dsimp [nullHomotopicMap, dNext, prevD]
  rw [C.shape]; rw [D.shape]; rw [zero_comp]; rw [comp_zero]; rw [add_zero] <;> apply_assumption

@[simp]

Depends on / 依赖: C.shape, D.shape, add_zero, apply_assumption, comp_zero, nullHomotopicMap, zero_comp
-/
theorem nullHomotopicMap_f_eq_zero {k₀ : ι} (hk₀ : forall l : ι, ¬c.Rel k₀ l)
    (hk₀' : forall l : ι, ¬c.Rel l k₀) (hom : forall i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₀ = 0 := by
  dsimp [nullHomotopicMap, dNext, prevD]
  rw [C.shape]; rw [D.shape]; rw [zero_comp]; rw [comp_zero]; rw [add_zero] <;> apply_assumption

@[simp]
/--
theorem `nullHomotopicMap'_f_eq_zero` / 定理 `nullHomotopicMap'_f_eq_zero`

English:
theorem nullHomotopicMap'_f_eq_zero
  statement: {k₀ : ι} (hk₀ : forall l : ι, ¬c.Rel k₀ l)
  proof: by
  simp only [nullHomotopicMap']
  apply nullHomotopicMap_f_eq_zero hk₀ hk₀'

中文:
定理 nullHomotopicMap'_f_eq_zero
  结论: {k₀ : ι} (hk₀ : 对任意 l : ι, ¬c.关系 k₀ l)
  证明: by
  simp only [nullHomotopicMap']
  apply nullHomotopicMap_f_eq_zero hk₀ hk₀'
-/
theorem nullHomotopicMap'_f_eq_zero {k₀ : ι} (hk₀ : forall l : ι, ¬c.Rel k₀ l)
    (hk₀' : forall l : ι, ¬c.Rel l k₀) (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₀ = 0 := by
  simp only [nullHomotopicMap']
  apply nullHomotopicMap_f_eq_zero hk₀ hk₀'

/-!
`Homotopy.mkInductive` allows us to build a homotopy of chain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `Homotopy e 0`.
`Homotopy.equivSubZero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eqToHom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/


section MkInductive

variable {P Q : ChainComplex V Nat}

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `prevD_chainComplex` / 定理 `prevD_chainComplex`

English:
theorem prevD_chainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j) (j : Nat)
  proof: by
  dsimp [prevD]
  have : (ComplexShape.down Nat).prev j = j + 1 := ChainComplex.prev Nat j
  congr 2

中文:
定理 prevD_chainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j) (j : 自然数)
  证明: by
  dsimp [prevD]
  have : (ComplexShape.down Nat).prev j = j + 1 := ChainComplex.prev Nat j
  congr 2

Depends on / 依赖: ChainComplex, ChainComplex.prev, ComplexShape, ComplexShape.down
-/
theorem prevD_chainComplex (f : forall i j, P.X i ⟶ Q.X j) (j : Nat) :
    prevD j f = f j (j + 1) ≫ Q.d _ _ := by
  dsimp [prevD]
  have : (ComplexShape.down Nat).prev j = j + 1 := ChainComplex.prev Nat j
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dNext_succ_chainComplex` / 定理 `dNext_succ_chainComplex`

English:
theorem dNext_succ_chainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j) (i : Nat)
  proof: by
  dsimp [dNext]
  have : (ComplexShape.down Nat).next (i + 1) = i := ChainComplex.next_nat_succ _
  congr 2

中文:
定理 dNext_succ_chainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j) (i : 自然数)
  证明: by
  dsimp [dNext]
  have : (ComplexShape.down Nat).next (i + 1) = i := ChainComplex.next_nat_succ _
  congr 2

Depends on / 依赖: ChainComplex, ChainComplex.next_nat_succ, ComplexShape, ComplexShape.down, next_nat_succ
-/
theorem dNext_succ_chainComplex (f : forall i j, P.X i ⟶ Q.X j) (i : Nat) :
    dNext (i + 1) f = P.d _ _ ≫ f i (i + 1) := by
  dsimp [dNext]
  have : (ComplexShape.down Nat).next (i + 1) = i := ChainComplex.next_nat_succ _
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dNext_zero_chainComplex` / 定理 `dNext_zero_chainComplex`

English:
theorem dNext_zero_chainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j)
  statement: dNext 0 f = 0
  proof: by
  dsimp [dNext]
  rw [P.shape]; rw [zero_comp]
  rw [ChainComplex.next_nat_zero]; dsimp; decide

中文:
定理 dNext_zero_chainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j)
  结论: dNext 0 f = 0
  证明: by
  dsimp [dNext]
  rw [P.shape]; rw [zero_comp]
  rw [ChainComplex.next_nat_zero]; dsimp; decide

Depends on / 依赖: ChainComplex, ChainComplex.next_nat_zero, P.shape, next_nat_zero, zero_comp
-/
theorem dNext_zero_chainComplex (f : forall i j, P.X i ⟶ Q.X j) : dNext 0 f = 0 := by
  dsimp [dNext]
  rw [P.shape]; rw [zero_comp]
  rw [ChainComplex.next_nat_zero]; dsimp; decide

variable (e : P ⟶ Q) (zero : P.X 0 ⟶ Q.X 1) (comm_zero : e.f 0 = zero ≫ Q.d 1 0)
  (one : P.X 1 ⟶ Q.X 2) (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ :
    forall (n : Nat)
      (p :
        Σ' (f : P.X n ⟶ Q.X (n + 1)) (f' : P.X (n + 1) ⟶ Q.X (n + 2)),
          e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 3),
        e.f (n + 2) = P.d (n + 2) (n + 1) ≫ p.2.1 + f'' ≫ Q.d (n + 3) (n + 2))

/-- An auxiliary construction for `mkInductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mkInductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `xNext` and `xPrev`,
which we do in `mkInductiveAux₂`.
-/
@[simp, nolint unusedArguments]
/--
Definition of `mkInductiveAux₁` / `mkInductiveAux₁` 的定义

English:
definition mkInductiveAux₁
  signature: :

中文:
定义 mkInductiveAux₁
  签名: :
-/
def mkInductiveAux₁ :
    forall n,
      Σ' (f : P.X n ⟶ Q.X (n + 1)) (f' : P.X (n + 1) ⟶ Q.X (n + 2)),
        e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mkInductiveAux₁ (n + 1)).2.1, (succ (n + 1) (mkInductiveAux₁ (n + 1))).1,
      (succ (n + 1) (mkInductiveAux₁ (n + 1))).2⟩

section

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mkInductiveAux₂` / `mkInductiveAux₂` 的定义

English:
definition mkInductiveAux₂
  signature: :
  body: mkInductiveAux₁ e zero --comm_zero
      one comm_one succ n
    ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩

中文:
定义 mkInductiveAux₂
  签名: :
  定义体: mkInductiveAux₁ e zero --comm_zero
      one comm_one succ n
    ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩

Depends on / 依赖: comm_zero
-/
def mkInductiveAux₂ :
    forall n, Σ' (f : P.xNext n ⟶ Q.X n) (f' : P.X n ⟶ Q.xPrev n), e.f n = P.dFrom n ≫ f + f' ≫ Q.dTo n
  | 0 => ⟨0, zero ≫ (Q.xPrevIso rfl).inv, by simpa using! comm_zero⟩
  | n + 1 =>
    let I := mkInductiveAux₁ e zero --comm_zero
      one comm_one succ n
    ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkInductiveAux₂_zero` / 定理 `mkInductiveAux₂_zero`

English:
theorem mkInductiveAux₂_zero
  proof: rfl

中文:
定理 mkInductiveAux₂_zero
  证明: rfl
-/
@[simp] theorem mkInductiveAux₂_zero :
    mkInductiveAux₂ e zero comm_zero one comm_one succ 0 =
      ⟨0, zero ≫ (Q.xPrevIso rfl).inv, by simpa using comm_zero⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkInductiveAux₂_add_one` / 定理 `mkInductiveAux₂_add_one`

English:
theorem mkInductiveAux₂_add_one
  given: (n)
  proof: mkInductiveAux₁ e zero one comm_one succ n
      ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩ :=
  rfl

中文:
定理 mkInductiveAux₂_add_one
  条件: (n)
  证明: mkInductiveAux₁ e zero one comm_one succ n
      ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩ :=
  rfl
-/
@[simp] theorem mkInductiveAux₂_add_one (n) :
    mkInductiveAux₂ e zero comm_zero one comm_one succ (n + 1) =
      letI I := mkInductiveAux₁ e zero one comm_one succ n
      ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkInductiveAux₃` / 定理 `mkInductiveAux₃`

English:
theorem mkInductiveAux₃
  given: (i j : Nat) (h : i + 1 = j)
  proof: by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkInductiveAux₂]

中文:
定理 mkInductiveAux₃
  条件: (i j : 自然数) (h : i + 1 = j)
  证明: by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkInductiveAux₂]
-/
theorem mkInductiveAux₃ (i j : Nat) (h : i + 1 = j) :
    (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom =
      (P.xNextIso h).inv ≫ (mkInductiveAux₂ e zero comm_zero one comm_one succ j).1 := by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkInductiveAux₂]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkInductive` / `mkInductive` 的定义

English:
definition mkInductive
  signature: : Homotopy e 0 where
  body: if h : i + 1 = j then
      (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    refine (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [fromNext, mkInductiveAux₂]
      · dsimp [fromNext]
        simp only [ChainComplex.next_nat_succ, dite_true]
        rw [mkInductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xNextIso]
        rw [id_comp]
    · dsimp [toPrev]
      rw [dif_pos (by simp only [ChainComplex.prev])]
      simp [xPrevIso, comp_id]

中文:
定义 mkInductive
  签名: : 同伦 e 0 where
  定义体: if h : i + 1 = j then
      (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    refine (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [fromNext, mkInductiveAux₂]
      · dsimp [fromNext]
        simp only [ChainComplex.next_nat_succ, dite_true]
        rw [mkInductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xNextIso]
        rw [id_comp]
    · dsimp [toPrev]
      rw [dif_pos (by simp only [ChainComplex.prev])]
      simp [xPrevIso, comp_id]

Depends on / 依赖: ChainComplex, ChainComplex.next_nat_succ, Q.xPrevIso, add_zero, comm_one, comm_zero, dif_neg, dif_pos, dite_true, fromNext, id_comp, next_nat_succ, toPrev, xNextIso, xPrevIso
-/
def mkInductive : Homotopy e 0 where
  hom i j :=
    if h : i + 1 = j then
      (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    refine (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [fromNext, mkInductiveAux₂]
      · dsimp [fromNext]
        simp only [ChainComplex.next_nat_succ, dite_true]
        rw [mkInductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xNextIso]
        rw [id_comp]
    · dsimp [toPrev]
      rw [dif_pos (by simp only [ChainComplex.prev])]
      simp [xPrevIso, comp_id]

end

end MkInductive

/-!
`Homotopy.mkCoinductive` allows us to build a homotopy of cochain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.
-/

section MkCoinductive

variable {P Q : CochainComplex V Nat}

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dNext_cochainComplex` / 定理 `dNext_cochainComplex`

English:
theorem dNext_cochainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j) (j : Nat)
  proof: by
  dsimp [dNext]
  have : (ComplexShape.up Nat).next j = j + 1 := CochainComplex.next Nat j
  congr 2

中文:
定理 dNext_cochainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j) (j : 自然数)
  证明: by
  dsimp [dNext]
  have : (ComplexShape.up Nat).next j = j + 1 := CochainComplex.next Nat j
  congr 2

Depends on / 依赖: CochainComplex, CochainComplex.next, ComplexShape, ComplexShape.up
-/
theorem dNext_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) (j : Nat) :
    dNext j f = P.d _ _ ≫ f (j + 1) j := by
  dsimp [dNext]
  have : (ComplexShape.up Nat).next j = j + 1 := CochainComplex.next Nat j
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `prevD_succ_cochainComplex` / 定理 `prevD_succ_cochainComplex`

English:
theorem prevD_succ_cochainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j) (i : Nat)
  proof: by
  dsimp [prevD]
  have : (ComplexShape.up Nat).prev (i + 1) = i := CochainComplex.prev_nat_succ i
  congr 2

中文:
定理 prevD_succ_cochainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j) (i : 自然数)
  证明: by
  dsimp [prevD]
  have : (ComplexShape.up Nat).prev (i + 1) = i := CochainComplex.prev_nat_succ i
  congr 2

Depends on / 依赖: CochainComplex, CochainComplex.prev_nat_succ, ComplexShape, ComplexShape.up, prev_nat_succ
-/
theorem prevD_succ_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) (i : Nat) :
    prevD (i + 1) f = f (i + 1) _ ≫ Q.d i (i + 1) := by
  dsimp [prevD]
  have : (ComplexShape.up Nat).prev (i + 1) = i := CochainComplex.prev_nat_succ i
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `prevD_zero_cochainComplex` / 定理 `prevD_zero_cochainComplex`

English:
theorem prevD_zero_cochainComplex
  given: (f : forall i j, P.X i ⟶ Q.X j)
  statement: prevD 0 f = 0
  proof: by
  dsimp [prevD]
  rw [Q.shape]; rw [comp_zero]
  rw [CochainComplex.prev_nat_zero]; dsimp; decide

中文:
定理 prevD_zero_cochainComplex
  条件: (f : 对任意 i j, P.X i ⟶ Q.X j)
  结论: prevD 0 f = 0
  证明: by
  dsimp [prevD]
  rw [Q.shape]; rw [comp_zero]
  rw [CochainComplex.prev_nat_zero]; dsimp; decide

Depends on / 依赖: CochainComplex, CochainComplex.prev_nat_zero, Q.shape, comp_zero, prev_nat_zero
-/
theorem prevD_zero_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) : prevD 0 f = 0 := by
  dsimp [prevD]
  rw [Q.shape]; rw [comp_zero]
  rw [CochainComplex.prev_nat_zero]; dsimp; decide

variable (e : P ⟶ Q) (zero : P.X 1 ⟶ Q.X 0) (comm_zero : e.f 0 = P.d 0 1 ≫ zero)
  (one : P.X 2 ⟶ Q.X 1) (comm_one : e.f 1 = zero ≫ Q.d 0 1 + P.d 1 2 ≫ one)
  (succ :
    forall (n : Nat)
      (p :
        Σ' (f : P.X (n + 1) ⟶ Q.X n) (f' : P.X (n + 2) ⟶ Q.X (n + 1)),
          e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'),
      Σ' f'' : P.X (n + 3) ⟶ Q.X (n + 2),
        e.f (n + 2) = p.2.1 ≫ Q.d (n + 1) (n + 2) + P.d (n + 2) (n + 3) ≫ f'')

/-- An auxiliary construction for `mkCoinductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mkCoinductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `xNext` and `xPrev`,
which we do in `mkInductiveAux₂`.
-/
@[simp]
/--
Definition of `mkCoinductiveAux₁` / `mkCoinductiveAux₁` 的定义

English:
definition mkCoinductiveAux₁
  signature: :

中文:
定义 mkCoinductiveAux₁
  签名: :

Depends on / 依赖: mapIso
-/
def mkCoinductiveAux₁ :
    forall n,
      Σ' (f : P.X (n + 1) ⟶ Q.X n) (f' : P.X (n + 2) ⟶ Q.X (n + 1)),
        e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mkCoinductiveAux₁ (n + 1)).2.1, (succ (n + 1) (mkCoinductiveAux₁ (n + 1))).1,
      (succ (n + 1) (mkCoinductiveAux₁ (n + 1))).2⟩

section

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mkCoinductiveAux₂` / `mkCoinductiveAux₂` 的定义

English:
definition mkCoinductiveAux₂
  signature: :
  body: mkCoinductiveAux₁ e zero one comm_one succ n
    ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩

中文:
定义 mkCoinductiveAux₂
  签名: :
  定义体: mkCoinductiveAux₁ e zero one comm_one succ n
    ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩

Depends on / 依赖: comm_one, mapIso
-/
def mkCoinductiveAux₂ :
    forall n, Σ' (f : P.X n ⟶ Q.xPrev n) (f' : P.xNext n ⟶ Q.X n), e.f n = f ≫ Q.dTo n + P.dFrom n ≫ f'
  | 0 => ⟨0, (P.xNextIso rfl).hom ≫ zero, by simpa using! comm_zero⟩
  | n + 1 =>
    let I := mkCoinductiveAux₁ e zero one comm_one succ n
    ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkCoinductiveAux₂_zero` / 定理 `mkCoinductiveAux₂_zero`

English:
theorem mkCoinductiveAux₂_zero
  proof: rfl

中文:
定理 mkCoinductiveAux₂_zero
  证明: rfl

Depends on / 依赖: mapIso
-/
@[simp] theorem mkCoinductiveAux₂_zero :
    mkCoinductiveAux₂ e zero comm_zero one comm_one succ 0 =
      ⟨0, (P.xNextIso rfl).hom ≫ zero, by simpa using comm_zero⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkCoinductiveAux₂_add_one` / 定理 `mkCoinductiveAux₂_add_one`

English:
theorem mkCoinductiveAux₂_add_one
  given: (n)
  proof: mkCoinductiveAux₁ e zero one comm_one succ n
      ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩ :=
  rfl

中文:
定理 mkCoinductiveAux₂_add_one
  条件: (n)
  证明: mkCoinductiveAux₁ e zero one comm_one succ n
      ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩ :=
  rfl
-/
@[simp] theorem mkCoinductiveAux₂_add_one (n) :
    mkCoinductiveAux₂ e zero comm_zero one comm_one succ (n + 1) =
      letI I := mkCoinductiveAux₁ e zero one comm_one succ n
      ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mkCoinductiveAux₃` / 定理 `mkCoinductiveAux₃`

English:
theorem mkCoinductiveAux₃
  given: (i j : Nat) (h : i + 1 = j)
  proof: by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkCoinductiveAux₂]

中文:
定理 mkCoinductiveAux₃
  条件: (i j : 自然数) (h : i + 1 = j)
  证明: by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkCoinductiveAux₂]
-/
theorem mkCoinductiveAux₃ (i j : Nat) (h : i + 1 = j) :
    (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.1 =
      (mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).1 ≫ (Q.xPrevIso h).hom := by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkCoinductiveAux₂]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkCoinductive` / `mkCoinductive` 的定义

English:
definition mkCoinductive
  signature: : Homotopy e 0 where
  body: if h : j + 1 = i then
      (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).2.1
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    rw [add_comm]
    refine (mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [toPrev, mkCoinductiveAux₂]
      · dsimp [toPrev]
        simp only [CochainComplex.prev_nat_succ, dite_true]
        rw [mkCoinductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xPrevIso]
        rw [comp_id]
    · dsimp [fromNext]
      rw [dif_pos (by simp only [CochainComplex.next])]
      simp [xNextIso, id_comp]

中文:
定义 mkCoinductive
  签名: : 同伦 e 0 where
  定义体: if h : j + 1 = i then
      (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).2.1
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    rw [add_comm]
    refine (mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [toPrev, mkCoinductiveAux₂]
      · dsimp [toPrev]
        simp only [CochainComplex.prev_nat_succ, dite_true]
        rw [mkCoinductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xPrevIso]
        rw [comp_id]
    · dsimp [fromNext]
      rw [dif_pos (by simp only [CochainComplex.next])]
      simp [xNextIso, id_comp]

Depends on / 依赖: CochainComplex, CochainComplex.prev_nat_succ, P.xNextIso, add_comm, add_zero, comm_one, comm_zero, comp_id, dif_neg, dite_true, prev_nat_succ, toPrev, xNextIso, xPrevIso
-/
def mkCoinductive : Homotopy e 0 where
  hom i j :=
    if h : j + 1 = i then
      (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).2.1
    else 0
  zero i j w := by rw [dif_neg]; exact w
  comm i := by
    dsimp
    simp only [add_zero]
    rw [add_comm]
    refine (mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.2.trans ?_
    congr
    · cases i
      · dsimp [toPrev, mkCoinductiveAux₂]
      · dsimp [toPrev]
        simp only [CochainComplex.prev_nat_succ, dite_true]
        rw [mkCoinductiveAux₃ e zero comm_zero one comm_one succ]
        dsimp [xPrevIso]
        rw [comp_id]
    · dsimp [fromNext]
      rw [dif_pos (by simp only [CochainComplex.next])]
      simp [xNextIso, id_comp]

end

end MkCoinductive

end Homotopy

/--
Definition of `HomotopyEquiv` / `HomotopyEquiv` 的定义

English:
structure HomotopyEquiv
  parameters: (C D : HomologicalComplex V c)
  axioms and operations (4):
    - hom : C ⟶ D
    - inv : D ⟶ C
    - homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 C)
    - homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 D)

中文:
结构 同伦等价
  参数: (C D : 同调复形 V c)
  公理与运算 (4 个):
    - hom : C ⟶ D
    - inv : D ⟶ C
    - homotopyHomInvId : 同伦 (hom ≫ inv) (𝟙 C)
    - homotopyInvHomId : 同伦 (inv ≫ hom) (𝟙 D)
-/
structure HomotopyEquiv (C D : HomologicalComplex V c) where
  /-- The forward chain map -/
  hom : C ⟶ D
  /-- The backward chain map -/
  inv : D ⟶ C
  /-- A homotopy showing that composing the forward and backward maps is homotopic to the identity
  on C -/
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 C)
  /-- A homotopy showing that composing the backward and forward maps is homotopic to the identity
  on D -/
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 D)

variable (V c) in
/--
Definition of `HomologicalComplex.homotopyEquivalences` / `HomologicalComplex.homotopyEquivalences` 的定义

English:
definition HomologicalComplex.homotopyEquivalences
  signature: :
  body: fun X Y f => exists (e : HomotopyEquiv X Y), e.hom = f

中文:
定义 同调复形.homotopyEquivalences
  签名: :
  定义体: fun X Y f => exists (e : HomotopyEquiv X Y), e.hom = f

Depends on / 依赖: HomotopyEquiv, e.hom
-/
def HomologicalComplex.homotopyEquivalences :
    MorphismProperty (HomologicalComplex V c) :=
  fun X Y f => exists (e : HomotopyEquiv X Y), e.hom = f

namespace HomotopyEquiv

variable {C D E : HomologicalComplex V c}

variable (C) in
/-- Any complex is homotopy equivalent to itself. -/
@[refl, simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : HomotopyEquiv C C where
  body: 𝟙 C
  inv := 𝟙 C
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

中文:
定义 refl
  签名: : 同伦等价 C C where
  定义体: 𝟙 C
  inv := 𝟙 C
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)
-/
def refl : HomotopyEquiv C C where
  hom := 𝟙 C
  inv := 𝟙 C
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomotopyEquiv C C)
  body: ⟨refl C⟩

中文:
实例 :
  签名: 可居 (同伦等价 C C)
  定义体: ⟨refl C⟩
-/
instance : Inhabited (HomotopyEquiv C C) :=
  ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm, simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : HomotopyEquiv C D)
  body: f.inv
  inv := f.hom
  homotopyHomInvId := f.homotopyInvHomId
  homotopyInvHomId := f.homotopyHomInvId

中文:
定义 symm
  签名: (f : 同伦等价 C D)
  定义体: f.inv
  inv := f.hom
  homotopyHomInvId := f.homotopyInvHomId
  homotopyInvHomId := f.homotopyHomInvId

Depends on / 依赖: f.inv
-/
def symm (f : HomotopyEquiv C D) : HomotopyEquiv D C where
  hom := f.inv
  inv := f.hom
  homotopyHomInvId := f.homotopyInvHomId
  homotopyInvHomId := f.homotopyHomInvId

/-- Homotopy equivalence is a transitive relation. -/
@[trans, simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : HomotopyEquiv C D) (g : HomotopyEquiv D E)
  body: f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  homotopyHomInvId := by simpa using
    ((g.homotopyHomInvId.compRightId f.inv).compLeft f.hom).trans f.homotopyHomInvId
  homotopyInvHomId := by simpa using
    ((f.homotopyInvHomId.compRightId g.hom).compLeft g.inv).trans g.homotopyInvHomId

中文:
定义 trans
  签名: (f : 同伦等价 C D) (g : 同伦等价 D E)
  定义体: f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  homotopyHomInvId := by simpa using
    ((g.homotopyHomInvId.compRightId f.inv).compLeft f.hom).trans f.homotopyHomInvId
  homotopyInvHomId := by simpa using
    ((f.homotopyInvHomId.compRightId g.hom).compLeft g.inv).trans g.homotopyInvHomId

Depends on / 依赖: f.hom, g.hom
-/
def trans (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) :
    HomotopyEquiv C E where
  hom := f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  homotopyHomInvId := by simpa using
    ((g.homotopyHomInvId.compRightId f.inv).compLeft f.hom).trans f.homotopyHomInvId
  homotopyInvHomId := by simpa using
    ((f.homotopyInvHomId.compRightId g.hom).compLeft g.inv).trans g.homotopyInvHomId

/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}
  body: ⟨f.hom, f.inv, Homotopy.ofEq f.3, Homotopy.ofEq f.4⟩

中文:
定义 ofIso
  签名: {ι : 类型} {V : 类型u} [范畴.{v} V] [预加性 V] {c : 余mplexShape ι}
  定义体: ⟨f.hom, f.inv, Homotopy.ofEq f.3, Homotopy.ofEq f.4⟩

Depends on / 依赖: Homotopy, Homotopy.ofEq, f.hom, f.inv
-/
def ofIso {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}
    {C D : HomologicalComplex V c} (f : C ≅ D) : HomotopyEquiv C D :=
  ⟨f.hom, f.inv, Homotopy.ofEq f.3, Homotopy.ofEq f.4⟩

/--
lemma `homotopyEquivalences_hom` / 引理 `homotopyEquivalences_hom`

English:
lemma homotopyEquivalences_hom
  given: (f : HomotopyEquiv C D)
  proof: ⟨f, rfl⟩

中文:
引理 homotopyEquivalences_hom
  条件: (f : 同伦等价 C D)
  证明: ⟨f, rfl⟩
-/
lemma homotopyEquivalences_hom (f : HomotopyEquiv C D) :
    homotopyEquivalences _ _ f.hom := ⟨f, rfl⟩

/--
lemma `homotopyEquivalences_inv` / 引理 `homotopyEquivalences_inv`

English:
lemma homotopyEquivalences_inv
  given: (f : HomotopyEquiv C D)
  proof: f.symm.homotopyEquivalences_hom

中文:
引理 homotopyEquivalences_inv
  条件: (f : 同伦等价 C D)
  证明: f.symm.homotopyEquivalences_hom

Depends on / 依赖: f.symm.homotopyEquivalences_hom, homotopyEquivalences_hom
-/
lemma homotopyEquivalences_inv (f : HomotopyEquiv C D) :
    homotopyEquivalences _ _ f.inv := f.symm.homotopyEquivalences_hom

/-- If `f` if a homotopy equivalence and `h` is a homotopy from `f.hom` to
a morphism `g`, then this is a homotopy equivalence whose `hom` field is `g`. -/
@[simps hom inv]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : HomotopyEquiv C D) {g : C ⟶ D} (h : Homotopy f.hom g)
  body: g
  inv := f.inv
  homotopyHomInvId := (h.symm.compRight _).trans f.homotopyHomInvId
  homotopyInvHomId := (h.symm.compLeft _).trans f.homotopyInvHomId

中文:
定义 copy
  签名: (f : 同伦等价 C D) {g : C ⟶ D} (h : 同伦 f.hom g)
  定义体: g
  inv := f.inv
  homotopyHomInvId := (h.symm.compRight _).trans f.homotopyHomInvId
  homotopyInvHomId := (h.symm.compLeft _).trans f.homotopyInvHomId
-/
def copy (f : HomotopyEquiv C D) {g : C ⟶ D} (h : Homotopy f.hom g) :
    HomotopyEquiv C D where
  hom := g
  inv := f.inv
  homotopyHomInvId := (h.symm.compRight _).trans f.homotopyHomInvId
  homotopyInvHomId := (h.symm.compLeft _).trans f.homotopyInvHomId

end HomotopyEquiv

namespace HomologicalComplex

/--
lemma `homotopyEquivalences.of_isIso` / 引理 `homotopyEquivalences.of_isIso`

English:
lemma homotopyEquivalences.of_isIso
  given: (f : C ⟶ D) [IsIso f]
  statement: homotopyEquivalences _ _ f
  proof: ⟨.ofIso (asIso f), rfl⟩

中文:
引理 homotopyEquivalences.of_isIso
  条件: (f : C ⟶ D) [是同构 f]
  结论: homotopyEquivalences _ _ f
  证明: ⟨.ofIso (asIso f), rfl⟩
-/
lemma homotopyEquivalences.of_isIso (f : C ⟶ D) [IsIso f] : homotopyEquivalences _ _ f :=
  ⟨.ofIso (asIso f), rfl⟩

/--
lemma `homotopyEquivalences.of_homotopy` / 引理 `homotopyEquivalences.of_homotopy`

English:
lemma homotopyEquivalences.of_homotopy
  statement: {f g : C ⟶ D} (h : homotopyEquivalences _ _ f)
  proof: by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.copy hfg, by simp⟩

中文:
引理 homotopyEquivalences.of_homotopy
  结论: {f g : C ⟶ D} (h : homotopyEquivalences _ _ f)
  证明: by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.copy hfg, by simp⟩

Depends on / 依赖: e.copy
-/
lemma homotopyEquivalences.of_homotopy {f g : C ⟶ D} (h : homotopyEquivalences _ _ f)
    (hfg : Homotopy f g) :
    homotopyEquivalences _ _ g := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.copy hfg, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (homotopyEquivalences V c).IsMultiplicative
  body: ⟨.refl _, rfl⟩
  comp_mem f g := by
    rintro ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.trans g, rfl⟩

中文:
实例 :
  签名: (homotopyEquivalences V c).是Multiplicative
  定义体: ⟨.refl _, rfl⟩
  comp_mem f g := by
    rintro ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.trans g, rfl⟩
-/
instance : (homotopyEquivalences V c).IsMultiplicative where
  id_mem K := ⟨.refl _, rfl⟩
  comp_mem f g := by
    rintro ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.trans g, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (homotopyEquivalences V c).HasTwoOutOfThreeProperty
  body: by
    rintro ⟨g, rfl⟩ ⟨e, he⟩
    refine (e.trans g.symm).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, Category.assoc]
    exact g.homotopyHomInvId.compLeftId f
  of_precomp _ g := by
    rintro ⟨f, rfl⟩ ⟨e, he⟩
    refine (f.symm.trans e).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, ← Category.assoc]
    exact f.homotopyInvHomId.compRightId g

中文:
实例 :
  签名: (homotopyEquivalences V c).有TwoOutOfThreeProperty
  定义体: by
    rintro ⟨g, rfl⟩ ⟨e, he⟩
    refine (e.trans g.symm).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, Category.assoc]
    exact g.homotopyHomInvId.compLeftId f
  of_precomp _ g := by
    rintro ⟨f, rfl⟩ ⟨e, he⟩
    refine (f.symm.trans e).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, ← Category.assoc]
    exact f.homotopyInvHomId.compRightId g

Depends on / 依赖: Category, Category.assoc, HomotopyEquiv, HomotopyEquiv.symm_hom, HomotopyEquiv.trans_hom, compLeftId, compRightId, e.trans, f.homotopyInvHomId.compRightId, f.symm.trans, g.homotopyHomInvId.compLeftId, g.symm, homotopyEquivalences_hom, homotopyEquivalences_hom.of_homotopy, homotopyHomInvId, homotopyInvHomId, of_homotopy, of_precomp, symm_hom, trans_hom
-/
instance : (homotopyEquivalences V c).HasTwoOutOfThreeProperty where
  of_postcomp f _ := by
    rintro ⟨g, rfl⟩ ⟨e, he⟩
    refine (e.trans g.symm).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, Category.assoc]
    exact g.homotopyHomInvId.compLeftId f
  of_precomp _ g := by
    rintro ⟨f, rfl⟩ ⟨e, he⟩
    refine (f.symm.trans e).homotopyEquivalences_hom.of_homotopy ?_
    simp only [HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, he, ← Category.assoc]
    exact f.homotopyInvHomId.compRightId g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (homotopyEquivalences V c).RespectsIso
  body: MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ _ => .of_isIso _)

中文:
实例 :
  签名: (homotopyEquivalences V c).RespectsIso
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ _ => .of_isIso _)

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, of_isIso, respectsIso_of_isStableUnderComposition
-/
instance : (homotopyEquivalences V c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ _ => .of_isIso _)

end HomologicalComplex

end

namespace CategoryTheory

variable {W : Type*} [Category* W] [Preadditive W]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An additive functor takes homotopies to homotopies. -/
@[simps]
/--
Definition of `Functor.mapHomotopy` / `Functor.mapHomotopy` 的定义

English:
definition Functor.mapHomotopy
  signature: (F : V ⥤ W) [F.Additive] {f g : C ⟶ D} (h : Homotopy f g)
  body: F.map (h.hom i j)
  zero i j w := by dsimp; rw [h.zero i j w, F.map_zero]
  comm i := by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    simp [H]

中文:
定义 函子.mapHomotopy
  签名: (F : V ⥤ W) [F.加性] {f g : C ⟶ D} (h : 同伦 f g)
  定义体: F.map (h.hom i j)
  zero i j w := by dsimp; rw [h.zero i j w, F.map_zero]
  comm i := by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    simp [H]

Depends on / 依赖: F.map, h.hom
-/
def Functor.mapHomotopy (F : V ⥤ W) [F.Additive] {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy ((F.mapHomologicalComplex c).map f) ((F.mapHomologicalComplex c).map g) where
  hom i j := F.map (h.hom i j)
  zero i j w := by dsimp; rw [h.zero i j w, F.map_zero]
  comm i := by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    simp [H]

/-- An additive functor preserves homotopy equivalences. -/
@[simps]
/--
Definition of `Functor.mapHomotopyEquiv` / `Functor.mapHomotopyEquiv` 的定义

English:
definition Functor.mapHomotopyEquiv
  signature: (F : V ⥤ W) [F.Additive] (h : HomotopyEquiv C D)
  body: (F.mapHomologicalComplex c).map h.hom
  inv := (F.mapHomologicalComplex c).map h.inv
  homotopyHomInvId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyHomInvId
  homotopyInvHomId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyInvHomId

中文:
定义 函子.mapHomotopyEquiv
  签名: (F : V ⥤ W) [F.加性] (h : 同伦等价 C D)
  定义体: (F.mapHomologicalComplex c).map h.hom
  inv := (F.mapHomologicalComplex c).map h.inv
  homotopyHomInvId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyHomInvId
  homotopyInvHomId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyInvHomId

Depends on / 依赖: F.mapHomologicalComplex, h.hom, mapHomologicalComplex
-/
def Functor.mapHomotopyEquiv (F : V ⥤ W) [F.Additive] (h : HomotopyEquiv C D) :
    HomotopyEquiv ((F.mapHomologicalComplex c).obj C) ((F.mapHomologicalComplex c).obj D) where
  hom := (F.mapHomologicalComplex c).map h.hom
  inv := (F.mapHomologicalComplex c).map h.inv
  homotopyHomInvId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyHomInvId
  homotopyInvHomId := by
    rw [← (F.mapHomologicalComplex c).map_comp]; rw [← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyInvHomId

end CategoryTheory

section

open HomologicalComplex CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}
  [DecidableRel c.Rel] {K L : HomologicalComplex C c} {f g : K ⟶ L}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Homotopy.toShortComplex` / `Homotopy.toShortComplex` 的定义

English:
definition Homotopy.toShortComplex
  signature: (ho : Homotopy f g) (i : ι)
  body: if c.Rel (c.prev i) i
    then ho.hom _ (c.prev (c.prev i)) ≫ L.d _ _
    else f.f _ - g.f _ - K.d _ i ≫ ho.hom i _
  h₁ := ho.hom _ _
  h₂ := ho.hom _ _
  h₃ :=
    if c.Rel i (c.next i)
    then K.d _ _ ≫ ho.hom (c.next (c.next i)) _
    else f.f _ - g.f _ - ho.hom _ i ≫ L.d _ _
  h₀_f := by
    split_ifs with h
    · dsimp
      simp only [assoc, d_comp_d, comp_zero]
    · dsimp
      rw [L.shape _ _ h]; rw [comp_zero]
  g_h₃ := by
    split_ifs with h
    · simp
    · dsimp
      rw [K.shape _ _ h]; rw [zero_comp]
  comm₁ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.prev i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => d K (c.prev i) j ≫ ho.hom j (c.prev i)) (c.next_eq' h)]
    · abel
  comm₂ := ho.comm i
  comm₃ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.next i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => ho.hom (c.next i) j ≫ L.d j (c.next i)) (c.prev_eq' h)]
    · abel

omit [DecidableRel c.Rel]

中文:
定义 同伦.toShortComplex
  签名: (ho : 同伦 f g) (i : ι)
  定义体: if c.Rel (c.prev i) i
    then ho.hom _ (c.prev (c.prev i)) ≫ L.d _ _
    else f.f _ - g.f _ - K.d _ i ≫ ho.hom i _
  h₁ := ho.hom _ _
  h₂ := ho.hom _ _
  h₃ :=
    if c.Rel i (c.next i)
    then K.d _ _ ≫ ho.hom (c.next (c.next i)) _
    else f.f _ - g.f _ - ho.hom _ i ≫ L.d _ _
  h₀_f := by
    split_ifs with h
    · dsimp
      simp only [assoc, d_comp_d, comp_zero]
    · dsimp
      rw [L.shape _ _ h]; rw [comp_zero]
  g_h₃ := by
    split_ifs with h
    · simp
    · dsimp
      rw [K.shape _ _ h]; rw [zero_comp]
  comm₁ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.prev i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => d K (c.prev i) j ≫ ho.hom j (c.prev i)) (c.next_eq' h)]
    · abel
  comm₂ := ho.comm i
  comm₃ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.next i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => ho.hom (c.next i) j ≫ L.d j (c.next i)) (c.prev_eq' h)]
    · abel

omit [DecidableRel c.Rel]

Depends on / 依赖: K.shape, L.shape, c.Rel, c.next, c.prev, comp_zero, d_comp_d, ho.comm, ho.hom, split_ifs, zero_comp
-/
noncomputable def Homotopy.toShortComplex (ho : Homotopy f g) (i : ι) :
    ShortComplex.Homotopy ((shortComplexFunctor C c i).map f)
      ((shortComplexFunctor C c i).map g) where
  h₀ :=
    if c.Rel (c.prev i) i
    then ho.hom _ (c.prev (c.prev i)) ≫ L.d _ _
    else f.f _ - g.f _ - K.d _ i ≫ ho.hom i _
  h₁ := ho.hom _ _
  h₂ := ho.hom _ _
  h₃ :=
    if c.Rel i (c.next i)
    then K.d _ _ ≫ ho.hom (c.next (c.next i)) _
    else f.f _ - g.f _ - ho.hom _ i ≫ L.d _ _
  h₀_f := by
    split_ifs with h
    · dsimp
      simp only [assoc, d_comp_d, comp_zero]
    · dsimp
      rw [L.shape _ _ h]; rw [comp_zero]
  g_h₃ := by
    split_ifs with h
    · simp
    · dsimp
      rw [K.shape _ _ h]; rw [zero_comp]
  comm₁ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.prev i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => d K (c.prev i) j ≫ ho.hom j (c.prev i)) (c.next_eq' h)]
    · abel
  comm₂ := ho.comm i
  comm₃ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.next i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => ho.hom (c.next i) j ≫ L.d j (c.next i)) (c.prev_eq' h)]
    · abel

omit [DecidableRel c.Rel]
/--
lemma `Homotopy.homologyMap_eq` / 引理 `Homotopy.homologyMap_eq`

English:
lemma Homotopy.homologyMap_eq
  given: (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: open scoped Classical in ShortComplex.Homotopy.homologyMap_congr (ho.toShortComplex i)

中文:
引理 同伦.homologyMap_eq
  条件: (ho : 同伦 f g) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: open scoped Classical in ShortComplex.Homotopy.homologyMap_congr (ho.toShortComplex i)

Depends on / 依赖: Classical, Homotopy, ShortComplex, ShortComplex.Homotopy.homologyMap_congr, ho.toShortComplex, homologyMap_congr, scoped, toShortComplex
-/
lemma Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    homologyMap f i = homologyMap g i :=
  open scoped Classical in ShortComplex.Homotopy.homologyMap_congr (ho.toShortComplex i)

/--
Definition of `HomotopyEquiv.toHomologyIso` / `HomotopyEquiv.toHomologyIso` 的定义

English:
definition HomotopyEquiv.toHomologyIso
  signature: (h : HomotopyEquiv K L) (i : ι)
  body: homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

中文:
定义 同伦等价.toHomologyIso
  签名: (h : 同伦等价 K L) (i : ι)
  定义体: homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

Depends on / 依赖: h.hom, homologyMap
-/
noncomputable def HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] : K.homology i ≅ L.homology i where
  hom := homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

end
