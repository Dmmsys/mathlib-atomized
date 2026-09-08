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

/-- The composition of `C.d i (c.next i) ≫ f (c.next i) i`. -/
/-
**dNext** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dNext (i : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X i ⟶ D.X i)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `C.d i (c.next i) ≫ f (c.next i) i`.
-/
def dNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => C.d i (c.next i) ≫ f (c.next i) i) fun _ _ =>
    Preadditive.comp_add _ _ _ _ _ _

/-- `f (c.next i) i`. -/
/-
**fromNext** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fromNext (i : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.xNext i ⟶ D.X i)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f (c.next i) i`.
-/
def fromNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.xNext i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => f (c.next i) i) fun _ _ => rfl

@[simp]
/-
**dNext_eq_dFrom_fromNext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dNext_eq_dFrom_fromNext (f : forall i j, C.X i ⟶ D.X j) (i : ι) : dNext i 
f = C.dFrom i ≫ fromNext i f
参数：f : forall i j, C.X i ⟶ D.X j；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dNext_eq_dFrom_fromNext (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) :
    dNext i f = C.dFrom i ≫ fromNext i f :=
  rfl
/-
**dNext_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dNext_eq (f : forall i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel i i') : dNe
xt i f = C.d i i' ≫ f i' i
参数：f : forall i j, C.X i ⟶ D.X j；w : c.Rel i i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
theorem dNext_eq (f : ∀ i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel i i') :
    dNext i f = C.d i i' ≫ f i' i := by
  obtain rfl := c.next_eq' w
  rfl

set_option backward.defeqAttrib.useBackward true in
/-
**dNext_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dNext_eq_zero (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel i (c.n
ext i)) : dNext i f = 0
参数：f : forall i j, C.X i ⟶ D.X j；i : ι；hi : ¬ c.Rel i (c.next i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma dNext_eq_zero (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    dNext i f = 0 := by
  dsimp [dNext]
  rw [shape _ _ _ hi, zero_comp]

-- This is not a simp lemma; the LHS already simplifies.
/-
**dNext_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dNext_comp_left (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (i : ι) : (dNe
xt i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g
参数：f : C ⟶ D；g : forall i j, D.X i ⟶ E.X j；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
-/
theorem dNext_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (i : ι) :
    (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g :=
  (f.comm_assoc _ _ _).symm

-- This is not a simp lemma; the LHS already simplifies.
/-
**dNext_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dNext_comp_right (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) : (dN
ext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i
参数：f : forall i j, C.X i ⟶ D.X j；g : D ⟶ E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem dNext_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
    (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i :=
  (assoc _ _ _).symm

/-- The composition `f j (c.prev j) ≫ D.d (c.prev j) j`. -/
/-
**prevD** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：prevD (j : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X j ⟶ D.X j)
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition `f j (c.prev j) ≫ D.d (c.prev j) j`.
-/
def prevD (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X j) :=
  AddMonoidHom.mk' (fun f => f j (c.prev j) ≫ D.d (c.prev j) j) fun _ _ =>
    Preadditive.add_comp _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**prevD_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prevD_eq_zero (f : forall i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel (c.pre
v i) i) : prevD i f = 0
参数：f : forall i j, C.X i ⟶ D.X j；i : ι；hi : ¬ c.Rel (c.prev i) i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma prevD_eq_zero (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel (c.prev i) i) :
    prevD i f = 0 := by
  dsimp [prevD]
  rw [shape _ _ _ hi, comp_zero]

/-- `f j (c.prev j)`. -/
/-
**toPrev** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toPrev (j : ι) : (forall i j, C.X i ⟶ D.X j) ->+ (C.X j ⟶ D.xPrev j)
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f j (c.prev j)`.
-/
def toPrev (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.xPrev j) :=
  AddMonoidHom.mk' (fun f => f j (c.prev j)) fun _ _ => rfl

@[simp]
/-
**prevD_eq_toPrev_dTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prevD_eq_toPrev_dTo (f : forall i j, C.X i ⟶ D.X j) (j : ι) : prevD j f = 
toPrev j f ≫ D.dTo j
参数：f : forall i j, C.X i ⟶ D.X j；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prevD_eq_toPrev_dTo (f : ∀ i j, C.X i ⟶ D.X j) (j : ι) :
    prevD j f = toPrev j f ≫ D.dTo j :=
  rfl
/-
**prevD_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prevD_eq (f : forall i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel j' j) : pre
vD j f = f j j' ≫ D.d j' j
参数：f : forall i j, C.X i ⟶ D.X j；w : c.Rel j' j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
-/
theorem prevD_eq (f : ∀ i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel j' j) :
    prevD j f = f j j' ≫ D.d j' j := by
  obtain rfl := c.prev_eq' w
  rfl

-- This is not a simp lemma; the LHS already simplifies.
/-
**prevD_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prevD_comp_left (f : C ⟶ D) (g : forall i j, D.X i ⟶ E.X j) (j : ι) : (pre
vD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g
参数：f : C ⟶ D；g : forall i j, D.X i ⟶ E.X j；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem prevD_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (j : ι) :
    (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g :=
  assoc _ _ _

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**prevD_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prevD_comp_right (f : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) : (pr
evD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j
参数：f : forall i j, C.X i ⟶ D.X j；g : D ⟶ E；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prevD_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
    (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j := by
  dsimp [prevD]
  simp only [assoc, g.comm]

set_option backward.defeqAttrib.useBackward true in
/-
**dNext_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dNext_nat (C D : ChainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ D.
X j) : dNext i f = C.d i (i - 1) ≫ f (i - 1) i
参数：C D : ChainComplex V Nat；i : Nat；f : forall i j, C.X i ⟶ D.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ChainComplex.next_nat_zero`：next_nat_zero : (ComplexShape.down Nat).next
 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ChainComplex.next_nat_succ`：next_nat_succ (i : Nat) : (ComplexShape.down
 Nat).next (i + 1) = i
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem dNext_nat (C D : ChainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
    dNext i f = C.d i (i - 1) ≫ f (i - 1) i := by
  dsimp [dNext]
  cases i
  · simp
  · congr <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**prevD_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prevD_nat (C D : CochainComplex V Nat) (i : Nat) (f : forall i j, C.X i ⟶ 
D.X j) : prevD i f = f i (i - 1) ≫ D.d (i - 1) i
参数：C D : CochainComplex V Nat；i : Nat；f : forall i j, C.X i ⟶ D.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CochainComplex.prev_nat_zero`：prev_nat_zero : (ComplexShape.up Nat).prev
 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CochainComplex.prev_nat_succ`：prev_nat_succ (i : Nat) : (ComplexShape.up
 Nat).prev (i + 1) = i
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem prevD_nat (C D : CochainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
    prevD i f = f i (i - 1) ≫ D.d (i - 1) i := by
  dsimp [prevD]
  cases i
  · simp
  · congr <;> simp

/-- A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.Rel j i`, satisfying the homotopy condition.
-/
@[ext]
/-
**Homotopy** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Homotopy (f g : C ⟶ D) where hom : forall i j, C.X i ⟶ D.X j zero : forall
 i j, ¬c.Rel j i -> hom i j = 0
参数：f g : C ⟶ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.
X i ⟶ D.X j`
which are zero unless `c.Rel j i`, satisfying the homotopy condition.
-/
structure Homotopy (f g : C ⟶ D) where
  hom : ∀ i j, C.X i ⟶ D.X j
  zero : ∀ i j, ¬c.Rel j i → hom i j = 0 := by cat_disch
  comm : ∀ i, f.f i = dNext i hom + prevD i hom + g.f i := by cat_disch

variable {f g}

namespace Homotopy

/-- `f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
/-
**Homotopy.equivSubZero** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：equivSubZero : Homotopy f g ≃ Homotopy (f - g) 0 where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.zero`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Cate
gory.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C
 D …

--- 原说明 ---
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
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
/-
**Homotopy.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：ofEq (h : f = g) : Homotopy f g where hom
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal chain maps are homotopic.
-/
def ofEq (h : f = g) : Homotopy f g where
  hom := 0
  zero _ _ _ := rfl

/-- Every chain map is homotopic to itself. -/
@[simps!, refl]
/-
**Homotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：refl (f : C ⟶ D) : Homotopy f f
参数：f : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every chain map is homotopic to itself.
-/
def refl (f : C ⟶ D) : Homotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps!, symm]
/-
**Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where hom
参数：h : Homotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is homotopic to `g` iff `g` is homotopic to `f`.
-/
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where
  hom := -h.hom
  zero i j w := by rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero]
  comm i := by
    rw [map_neg, map_neg, h.comm, ← neg_add, ← add_assoc, neg_add_cancel, zero_add]

/-- homotopy is a transitive relation. -/
@[simps!, trans]
/-
**Homotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g
 where hom
参数：h : Homotopy e f；k : Homotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
homotopy is a transitive relation.
-/
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g where
  hom := h.hom + k.hom
  zero i j w := by rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_add]
  comm i := by grind [Homotopy.comm]

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps!]
/-
**Homotopy.add** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Ho
motopy (f₁ + f₂) (g₁ + g₂) where hom
参数：h₁ : Homotopy f₁ g₁；h₂ : Homotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the sum of two homotopies is a homotopy between the sum of the respective morphi
sms.
-/
def add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  zero i j hij := by rw [Pi.add_apply, Pi.add_apply, h₁.zero i j hij, h₂.zero i j hij, add_zero]
  comm i := by grind [HomologicalComplex.add_f_apply, Homotopy.comm]

set_option backward.defeqAttrib.useBackward true in
/-- the scalar multiplication of a homotopy -/
@[simps!]
/-
**Homotopy.smul** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：smul {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R) : Ho
motopy (a • f) (a • g) where hom i j
参数：h : Homotopy f g；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the scalar multiplication of a homotopy
-/
def smul {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R) :
    Homotopy (a • f) (a • g) where
  hom i j := a • h.hom i j
  zero i j hij := by
    rw [h.zero i j hij, smul_zero]
  comm i := by
    dsimp
    rw [h.comm]
    dsimp [fromNext, toPrev]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]

/-- homotopy is closed under composition (on the right) -/
@[simps]
/-
**Homotopy.compRight** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：compRight {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) 
(f ≫ g) where hom i j
参数：h : Homotopy e f；g : D ⟶ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
homotopy is closed under composition (on the right)
-/
def compRight {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) where
  hom i j := h.hom i j ≫ g.f j
  zero i j w := by rw [h.zero i j w, zero_comp]
  comm i := by rw [comp_f, h.comm i, dNext_comp_right, prevD_comp_right, Preadditive.add_comp,
    comp_f, Preadditive.add_comp]

/-- homotopy is closed under composition (on the left) -/
@[simps]
/-
**Homotopy.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：compLeft {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (
e ≫ g) where hom i j
参数：h : Homotopy f g；e : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
homotopy is closed under composition (on the left)
-/
def compLeft {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) where
  hom i j := e.f i ≫ h.hom i j
  zero i j w := by rw [h.zero i j w, comp_zero]
  comm i := by rw [comp_f, h.comm i, dNext_comp_left, prevD_comp_left, comp_f,
    Preadditive.comp_add, Preadditive.comp_add]

/-- homotopy is closed under composition -/
@[simps!]
/-
**Homotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C
₃} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂)
参数：h₁ : Homotopy f₁ g₁；h₂ : Homotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
homotopy is closed under composition
-/
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
    (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- a variant of `Homotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**Homotopy.compRightId** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：compRightId {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫
 g) g
参数：h : Homotopy f (𝟙 C)；g : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a variant of `Homotopy.compRight` useful for dealing with homotopy equivalences.
-/
def compRightId {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- a variant of `Homotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**Homotopy.compLeftId** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：compLeftId {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ 
f) g
参数：h : Homotopy f (𝟙 D)；g : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a variant of `Homotopy.compLeft` useful for dealing with homotopy equivalences.
-/
def compLeftId {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

/-!
Null homotopic maps can be constructed using the formula `hd+dh`. We show that
these morphisms are homotopic to `0` and provide some convenient simplification
lemmas that give a degreewise description of `hd+dh`, depending on whether we have
two differentials going to and from a certain degree, only one, or none.
-/


/-- The null homotopic map associated to a family `hom` of morphisms `C_i ⟶ D_j`.
This is the same datum as for the field `hom` in the structure `Homotopy`. For
this definition, we do not need the field `zero` of that structure
as this definition uses only the maps `C_i ⟶ C_j` when `c.Rel j i`. -/
/-
**Homotopy.nullHomotopicMap** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopicMap (hom : forall i j, C.X i ⟶ D.X j) : C ⟶ D where f i
参数：hom : forall i j, C.X i ⟶ D.X j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The null homotopic map associated to a family `hom` of morphisms `C_i ⟶ D_j`.
This is the same datum as for the field `hom` in the structure `Homotopy`. For
this definition, we do not need the field `zero` of that structure
as this definition uses only the maps `C_i ⟶ C_j` when `c.Rel j i`.
-/
def nullHomotopicMap (hom : ∀ i j, C.X i ⟶ D.X j) : C ⟶ D where
  f i := dNext i hom + prevD i hom
  comm' i j hij := by
    have eq1 : prevD i hom ≫ D.d i j = 0 := by
      simp only [prevD, AddMonoidHom.mk'_apply, assoc, d_comp_d, comp_zero]
    have eq2 : C.d i j ≫ dNext j hom = 0 := by
      simp only [dNext, AddMonoidHom.mk'_apply, d_comp_d_assoc, zero_comp]
    rw [dNext_eq hom hij, prevD_eq hom hij, Preadditive.comp_add, Preadditive.add_comp, eq1, eq2,
      add_zero, zero_add, assoc]

open scoped Classical in
/-- Variant of `nullHomotopicMap` where the input consists only of the
relevant maps `C_i ⟶ D_j` such that `c.Rel j i`. -/
/-
**Homotopy.nullHomotopicMap'** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopicMap' (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) : C ⟶ D
参数：h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `nullHomotopicMap` where the input consists only of the
relevant maps `C_i ⟶ D_j` such that `c.Rel j i`.
-/
def nullHomotopicMap' (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) : C ⟶ D :=
  nullHomotopicMap fun i j => dite (c.Rel j i) (h i j) fun _ => 0

set_option backward.defeqAttrib.useBackward true in
/-- Compatibility of `nullHomotopicMap` with the postcomposition by a morphism
of complexes. -/
/-
**Homotopy.nullHomotopicMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopicMap_comp (hom : forall i j, C.X i ⟶ D.X j) (g : D ⟶ E) : null
HomotopicMap hom ≫ g = nullHomotopicMap fun i j => hom i j ≫ g.f j
参数：hom : forall i j, C.X i ⟶ D.X j；g : D ⟶ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compatibility of `nullHomotopicMap` with the postcomposition by a morphism
of complexes.
-/
theorem nullHomotopicMap_comp (hom : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) :
    nullHomotopicMap hom ≫ g = nullHomotopicMap fun i j => hom i j ≫ g.f j := by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.add_comp, assoc, g.comm]

/-- Compatibility of `nullHomotopicMap'` with the postcomposition by a morphism
of complexes. -/
/-
**Homotopy.nullHomotopicMap'_comp** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D E : Homologica
lComplex V c} (hom : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E),   Cat
egoryTheory.CategoryStruct.comp (Homotopy.nullHomotopicMap' hom) g =     Homotop
y.nullHomotopicMap' fun i j hij => CategoryTheory.CategoryStruct.comp (hom i j h
ij) (g.f j)
参数：hom : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X j)；g : D ⟶ E；Homotopy.nullHomotopi
cMap' hom；hom i j hij；g.f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap'.eq_1`：∀ {ι : Type u_1} {V : Type u} [inst : C
ategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : 
ComplexShape ι} {C D …
· 使用定理 `Homotopy.nullHomotopicMap_comp`：nullHomotopicMap_comp (hom : forall i j,
 C.X i ⟶ D.X j) (g : D ⟶ E) : nullHomotopicMap hom ≫ g = nullHomotopicMap fun i 
j => hom i j ≫ g.f j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

--- 原说明 ---
Compatibility of `nullHomotopicMap'` with the postcomposition by a morphism
of complexes.
-/
theorem nullHomotopicMap'_comp (hom : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E) :
    nullHomotopicMap' hom ≫ g = nullHomotopicMap' fun i j hij => hom i j hij ≫ g.f j := by
  rw [nullHomotopicMap', nullHomotopicMap_comp]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [zero_comp]

set_option backward.defeqAttrib.useBackward true in
/-- Compatibility of `nullHomotopicMap` with the precomposition by a morphism
of complexes. -/
/-
**Homotopy.comp_nullHomotopicMap** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：comp_nullHomotopicMap (f : C ⟶ D) (hom : forall i j, D.X i ⟶ E.X j) : f ≫ 
nullHomotopicMap hom = nullHomotopicMap fun i j => f.f i ≫ hom i j
参数：f : C ⟶ D；hom : forall i j, D.X i ⟶ E.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compatibility of `nullHomotopicMap` with the precomposition by a morphism
of complexes.
-/
theorem comp_nullHomotopicMap (f : C ⟶ D) (hom : ∀ i j, D.X i ⟶ E.X j) :
    f ≫ nullHomotopicMap hom = nullHomotopicMap fun i j => f.f i ≫ hom i j := by
  ext n
  dsimp [nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.comp_add, assoc, f.comm_assoc]

/-- Compatibility of `nullHomotopicMap'` with the precomposition by a morphism
of complexes. -/
/-
**Homotopy.comp_nullHomotopicMap'** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：comp_nullHomotopicMap' (f : C ⟶ D) (hom : forall i j, c.Rel j i -> (D.X i 
⟶ E.X j)) : f ≫ nullHomotopicMap' hom = nullHomotopicMap' fun i j hij => f.f i ≫
 hom i j hij
参数：f : C ⟶ D；hom : forall i j, c.Rel j i -> (D.X i ⟶ E.X j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap'.eq_1`：∀ {ι : Type u_1} {V : Type u} [inst : C
ategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : 
ComplexShape ι} {C D …
· 使用定理 `Homotopy.comp_nullHomotopicMap`：comp_nullHomotopicMap (f : C ⟶ D) (hom :
 forall i j, D.X i ⟶ E.X j) : f ≫ nullHomotopicMap hom = nullHomotopicMap fun i 
j => f.f i ≫ hom i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)

--- 原说明 ---
Compatibility of `nullHomotopicMap'` with the precomposition by a morphism
of complexes.
-/
theorem comp_nullHomotopicMap' (f : C ⟶ D) (hom : ∀ i j, c.Rel j i → (D.X i ⟶ E.X j)) :
    f ≫ nullHomotopicMap' hom = nullHomotopicMap' fun i j hij => f.f i ≫ hom i j hij := by
  rw [nullHomotopicMap', comp_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of `nullHomotopicMap` with the application of additive functors -/
/-
**Homotopy.map_nullHomotopicMap** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：map_nullHomotopicMap {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W)
 [G.Additive] (hom : forall i j, C.X i ⟶ D.X j) : (G.mapHomologicalComplex c).ma
p (nullHomotopicMap hom) = nullHomotopicMap (fun i j => by exact G.map (hom i j)
)
参数：G : V ⥤ W；hom : forall i j, C.X i ⟶ D.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compatibility of `nullHomotopicMap` with the application of additive functors
-/
theorem map_nullHomotopicMap {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, C.X i ⟶ D.X j) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap hom) =
      nullHomotopicMap (fun i j => by exact G.map (hom i j)) := by
  ext i
  dsimp [nullHomotopicMap, dNext, prevD]
  simp only [G.map_comp, Functor.map_add]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of `nullHomotopicMap'` with the application of additive functors -/
/-
**Homotopy.map_nullHomotopicMap'** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：map_nullHomotopicMap' {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W
) [G.Additive] (hom : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) : (G.mapHomologi
calComplex c).map (nullHomotopicMap' hom) = nullHomotopicMap' fun i j hij => by 
exact G.map (hom i j hij)
参数：G : V ⥤ W；hom : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap'.eq_1`：∀ {ι : Type u_1} {V : Type u} [inst : C
ategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : 
ComplexShape ι} {C D …
· 使用定理 `Homotopy.map_nullHomotopicMap`：map_nullHomotopicMap {W : Type*} [Categor
y* W] [Preadditive W] (G : V ⥤ W) [G.Additive] (hom : forall i j, C.X i ⟶ D.X j)
 : (G.mapHomologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…

--- 原说明 ---
Compatibility of `nullHomotopicMap'` with the application of additive functors
-/
theorem map_nullHomotopicMap' {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (G.mapHomologicalComplex c).map (nullHomotopicMap' hom) =
      nullHomotopicMap' fun i j hij => by exact G.map (hom i j hij) := by
  rw [nullHomotopicMap', map_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [G.map_zero]

/-- Tautological construction of the `Homotopy` to zero for maps constructed by
`nullHomotopicMap`, at least when we have the `zero` condition. -/
@[simps]
/-
**Homotopy.nullHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopy (hom : forall i j, C.X i ⟶ D.X j) (zero : forall i j, ¬c.Rel 
j i -> hom i j = 0) : Homotopy (nullHomotopicMap hom) 0
参数：hom : forall i j, C.X i ⟶ D.X j；zero : forall i j, ¬c.Rel j i -> hom i j = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tautological construction of the `Homotopy` to zero for maps constructed by
`nullHomotopicMap`, at least when we have the `zero` condition.
-/
def nullHomotopy (hom : ∀ i j, C.X i ⟶ D.X j) (zero : ∀ i j, ¬c.Rel j i → hom i j = 0) :
    Homotopy (nullHomotopicMap hom) 0 :=
  { hom := hom
    zero := zero
    comm := by
      intro i
      rw [HomologicalComplex.zero_f_apply, add_zero]
      rfl }

open scoped Classical in
/-- Homotopy to zero for maps constructed with `nullHomotopicMap'` -/
@[simps!]
/-
**Homotopy.nullHomotopy'** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopy' (h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)) : Homotopy (n
ullHomotopicMap' h) 0
参数：h : forall i j, c.Rel j i -> (C.X i ⟶ D.X j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy to zero for maps constructed with `nullHomotopicMap'`
-/
def nullHomotopy' (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) : Homotopy (nullHomotopicMap' h) 0 := by
  apply nullHomotopy fun i j => dite (c.Rel j i) (h i j) fun _ => 0
  grind

/-! This lemma and the following ones can be used in order to compute
the degreewise morphisms induced by the null homotopic maps constructed
with `nullHomotopicMap` or `nullHomotopicMap'` -/


-- Cannot be @[simp] because `k₀` and `k₂` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap_f** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopicMap_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀) 
(hom : forall i j, C.X i ⟶ D.X j) : (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ ho
m k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁
参数：r₂₁ : c.Rel k₂ k₁；r₁₀ : c.Rel k₁ k₀；hom : forall i j, C.X i ⟶ D.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dNext_eq`：dNext_eq (f : forall i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel
 i i') : dNext i f = C.d i i' ≫ f i' i
· 使用定理 `prevD_eq`：prevD_eq (f : forall i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel
 j' j) : prevD j f = f j j' ≫ D.d j' j
-/
theorem nullHomotopicMap_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (hom : ∀ i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ := by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀, prevD_eq hom r₂₁]

-- Cannot be @[simp] because `k₀` and `k₂` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap'_f** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)   (h : (i j :
 ι) → c.Rel j i → (C.X i ⟶ D.X j)),   (Homotopy.nullHomotopicMap' h).f k₁ =     
CategoryTheory.CategoryStruct.comp (C.d k₁ k₀) (h k₀ k₁ r₁₀) +       CategoryThe
ory.CategoryStruct.comp (h k₁ k₂ r₂₁) (D.d k₂ k₁)
参数：r₂₁ : c.Rel k₂ k₁；r₁₀ : c.Rel k₁ k₀；h : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X 
j)；Homotopy.nullHomotopicMap' h；C.d k₁ k₀；h k₀ k₁ r₁₀；h k₁ k₂ r₂₁；D.d k₂ k₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap_f`：nullHomotopicMap_f {k₂ k₁ k₀ : ι} (r₂₁ : c.
Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀) (hom : forall i j, C.X i ⟶ D.X j) : (nullHomotopi
cMap hom).f k₁ = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem nullHomotopicMap'_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ + h k₁ k₂ r₂₁ ≫ D.d k₂ k₁ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f r₂₁ r₁₀]
  split_ifs
  rfl

-- Cannot be @[simp] because `k₁` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap_f_of_not_rel_left** 是 Mathlib 中的一个定理，位于命名空间 `Homotop
y`。
形式化陈述：nullHomotopicMap_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₀ : 
forall l : ι, ¬c.Rel k₀ l) (hom : forall i j, C.X i ⟶ D.X j) : (nullHomotopicMap
 hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀
参数：r₁₀ : c.Rel k₁ k₀；hk₀ : forall l : ι, ¬c.Rel k₀ l；hom : forall i j, C.X i ⟶ D
.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `prevD_eq`：prevD_eq (f : forall i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel
 j' j) : prevD j f = f j j' ≫ D.d j' j
· 使用定理 `dNext.eq_1`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Categor
y.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D 
…
· 使用定理 `AddMonoidHom.mk'_apply`：∀ {M : Type u_4} {G : Type u_7} [inst : AddGroup
 G] [inst_1 : AddZeroClass M] (f : M → G)   (map_add : ∀ (a b : M), f (a + b) = 
f a + f b), …
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem nullHomotopicMap_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ := by
  dsimp only [nullHomotopicMap]
  rw [prevD_eq hom r₁₀, dNext, AddMonoidHom.mk'_apply, C.shape, zero_comp, zero_add]
  exact hk₀ _

-- Cannot be @[simp] because `k₁` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap'_f_of_not_rel_left** 是 Mathlib 中的一个定理，位于命名空间 `Homoto
py`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀),   (∀ (l : ι), ¬c.Rel k₀ l) →     ∀ 
(h : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X j)),       (Homotopy.nullHomotopicMap'
 h).f k₀ = CategoryTheory.CategoryStruct.comp (h k₀ k₁ r₁₀) (D.d k₁ k₀)
参数：r₁₀ : c.Rel k₁ k₀；∀ (l : ι), ¬c.Rel k₀ l；h : (i j : ι) → c.Rel j i → (C.X i ⟶
 D.X j)；Homotopy.nullHomotopicMap' h；h k₀ k₁ r₁₀；D.d k₁ k₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap_f_of_not_rel_left`：nullHomotopicMap_f_of_not_r
el_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₀ : forall l : ι, ¬c.Rel k₀ l) (hom :
 forall i j, C.X i ⟶ D.X j) : (nu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem nullHomotopicMap'_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_left r₁₀ hk₀]
  split_ifs
  rfl

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap_f_of_not_rel_right** 是 Mathlib 中的一个定理，位于命名空间 `Homoto
py`。
形式化陈述：nullHomotopicMap_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₁ :
 forall l : ι, ¬c.Rel l k₁) (hom : forall i j, C.X i ⟶ D.X j) : (nullHomotopicMa
p hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁
参数：r₁₀ : c.Rel k₁ k₀；hk₁ : forall l : ι, ¬c.Rel l k₁；hom : forall i j, C.X i ⟶ D
.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dNext_eq`：dNext_eq (f : forall i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel
 i i') : dNext i f = C.d i i' ≫ f i' i
· 使用定理 `prevD.eq_1`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Categor
y.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D 
…
· 使用定理 `AddMonoidHom.mk'_apply`：∀ {M : Type u_4} {G : Type u_7} [inst : AddGroup
 G] [inst_1 : AddZeroClass M] (f : M → G)   (map_add : ∀ (a b : M), f (a + b) = 
f a + f b), …
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem nullHomotopicMap_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : ∀ l : ι, ¬c.Rel l k₁) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ := by
  dsimp only [nullHomotopicMap]
  rw [dNext_eq hom r₁₀, prevD, AddMonoidHom.mk'_apply, D.shape, comp_zero, add_zero]
  exact hk₁ _

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.
/-
**Homotopy.nullHomotopicMap'_f_of_not_rel_right** 是 Mathlib 中的一个定理，位于命名空间 `Homot
opy`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀),   (∀ (l : ι), ¬c.Rel l k₁) →     ∀ 
(h : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X j)),       (Homotopy.nullHomotopicMap'
 h).f k₁ = CategoryTheory.CategoryStruct.comp (C.d k₁ k₀) (h k₀ k₁ r₁₀)
参数：r₁₀ : c.Rel k₁ k₀；∀ (l : ι), ¬c.Rel l k₁；h : (i j : ι) → c.Rel j i → (C.X i ⟶
 D.X j)；Homotopy.nullHomotopicMap' h；C.d k₁ k₀；h k₀ k₁ r₁₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.nullHomotopicMap_f_of_not_rel_right`：nullHomotopicMap_f_of_not_
rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀) (hk₁ : forall l : ι, ¬c.Rel l k₁) (hom
 : forall i j, C.X i ⟶ D.X j) : (n…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem nullHomotopicMap'_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : ∀ l : ι, ¬c.Rel l k₁) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ := by
  simp only [nullHomotopicMap']
  rw [nullHomotopicMap_f_of_not_rel_right r₁₀ hk₁]
  split_ifs
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**Homotopy.nullHomotopicMap_f_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：nullHomotopicMap_f_eq_zero {k₀ : ι} (hk₀ : forall l : ι, ¬c.Rel k₀ l) (hk₀
' : forall l : ι, ¬c.Rel l k₀) (hom : forall i j, C.X i ⟶ D.X j) : (nullHomotopi
cMap hom).f k₀ = 0
参数：hk₀ : forall l : ι, ¬c.Rel k₀ l；hk₀' : forall l : ι, ¬c.Rel l k₀；hom : forall
 i j, C.X i ⟶ D.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem nullHomotopicMap_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (hk₀' : ∀ l : ι, ¬c.Rel l k₀) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (nullHomotopicMap hom).f k₀ = 0 := by
  dsimp [nullHomotopicMap, dNext, prevD]
  rw [C.shape, D.shape, zero_comp, comp_zero, add_zero] <;> apply_assumption

@[simp]
/-
**Homotopy.nullHomotopicMap'_f_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} {k₀ : ι},   (∀ (l : ι), ¬c.Rel k₀ l) →     (∀ (l : ι), ¬c.Rel l k₀) 
→ ∀ (h : (i j : ι) → c.Rel j i → (C.X i ⟶ D.X j)), (Homotopy.nullHomotopicMap' h
).f k₀ = 0
参数：∀ (l : ι), ¬c.Rel k₀ l；∀ (l : ι), ¬c.Rel l k₀；h : (i j : ι) → c.Rel j i → (C.
X i ⟶ D.X j)；Homotopy.nullHomotopicMap' h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.nullHomotopicMap_f_eq_zero`：nullHomotopicMap_f_eq_zero {k₀ : ι}
 (hk₀ : forall l : ι, ¬c.Rel k₀ l) (hk₀' : forall l : ι, ¬c.Rel l k₀) (hom : for
all i j, C.X i ⟶ D.X j) :…
-/
theorem nullHomotopicMap'_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (hk₀' : ∀ l : ι, ¬c.Rel l k₀) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
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

variable {P Q : ChainComplex V ℕ}

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.prevD_chainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：prevD_chainComplex (f : forall i j, P.X i ⟶ Q.X j) (j : Nat) : prevD j f =
 f j (j + 1) ≫ Q.d _ _
参数：f : forall i j, P.X i ⟶ Q.X j；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ChainComplex.prev`：prev (α : Type*) [AddRightCancelSemigroup α] [One α] 
(i : α) : (ComplexShape.down α).prev i = i + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem prevD_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) :
    prevD j f = f j (j + 1) ≫ Q.d _ _ := by
  dsimp [prevD]
  have : (ComplexShape.down ℕ).prev j = j + 1 := ChainComplex.prev ℕ j
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.dNext_succ_chainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：dNext_succ_chainComplex (f : forall i j, P.X i ⟶ Q.X j) (i : Nat) : dNext 
(i + 1) f = P.d _ _ ≫ f i (i + 1)
参数：f : forall i j, P.X i ⟶ Q.X j；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ChainComplex.next_nat_succ`：next_nat_succ (i : Nat) : (ComplexShape.down
 Nat).next (i + 1) = i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem dNext_succ_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) :
    dNext (i + 1) f = P.d _ _ ≫ f i (i + 1) := by
  dsimp [dNext]
  have : (ComplexShape.down ℕ).next (i + 1) = i := ChainComplex.next_nat_succ _
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.dNext_zero_chainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：dNext_zero_chainComplex (f : forall i j, P.X i ⟶ Q.X j) : dNext 0 f = 0
参数：f : forall i j, P.X i ⟶ Q.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ChainComplex.next_nat_zero`：next_nat_zero : (ComplexShape.down Nat).next
 0 = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem dNext_zero_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) : dNext 0 f = 0 := by
  dsimp [dNext]
  rw [P.shape, zero_comp]
  rw [ChainComplex.next_nat_zero]; dsimp; decide

variable (e : P ⟶ Q) (zero : P.X 0 ⟶ Q.X 1) (comm_zero : e.f 0 = zero ≫ Q.d 1 0)
  (one : P.X 1 ⟶ Q.X 2) (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ :
    ∀ (n : ℕ)
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
/-
**Homotopy.mkInductiveAux** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkInductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agre
e.
They do in fact agree, and we then capture that at the type level (i.e. by const
ructing a homotopy)
in `mkInductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `xNext` and `xPrev`
,
which we do in `mkInductiveAux₂`.
-/
def mkInductiveAux₁ :
    ∀ n,
      Σ' (f : P.X n ⟶ Q.X (n + 1)) (f' : P.X (n + 1) ⟶ Q.X (n + 2)),
        e.f (n + 1) = P.d (n + 1) n ≫ f + f' ≫ Q.d (n + 2) (n + 1)
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mkInductiveAux₁ (n + 1)).2.1, (succ (n + 1) (mkInductiveAux₁ (n + 1))).1,
      (succ (n + 1) (mkInductiveAux₁ (n + 1))).2⟩

section

set_option backward.isDefEq.respectTransparency.types false in
/-- An auxiliary construction for `mkInductive`.
-/
/-
**Homotopy.mkInductiveAux** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkInductive`.
-/
def mkInductiveAux₂ :
    ∀ n, Σ' (f : P.xNext n ⟶ Q.X n) (f' : P.X n ⟶ Q.xPrev n), e.f n = P.dFrom n ≫ f + f' ≫ Q.dTo n
  | 0 => ⟨0, zero ≫ (Q.xPrevIso rfl).inv, by simpa using! comm_zero⟩
  | n + 1 =>
    let I := mkInductiveAux₁ e zero --comm_zero
      one comm_one succ n
    ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkInductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mkInductiveAux₂_zero :
    mkInductiveAux₂ e zero comm_zero one comm_one succ 0 =
      ⟨0, zero ≫ (Q.xPrevIso rfl).inv, by simpa using comm_zero⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkInductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mkInductiveAux₂_add_one (n) :
    mkInductiveAux₂ e zero comm_zero one comm_one succ (n + 1) =
      letI I := mkInductiveAux₁ e zero one comm_one succ n
      ⟨(P.xNextIso rfl).hom ≫ I.1, I.2.1 ≫ (Q.xPrevIso rfl).inv, by simpa using! I.2.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkInductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkInductiveAux₃ (i j : ℕ) (h : i + 1 = j) :
    (mkInductiveAux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.xPrevIso h).hom =
      (P.xNextIso h).inv ≫ (mkInductiveAux₂ e zero comm_zero one comm_one succ j).1 := by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkInductiveAux₂]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A constructor for a `Homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
/-
**Homotopy.mkInductive** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：mkInductive : Homotopy e 0 where hom i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for a `Homotopy e 0`, for `e` a chain map between `ℕ`-indexed chai
n complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previou
s two components.
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

variable {P Q : CochainComplex V ℕ}

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.dNext_cochainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：dNext_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) (j : Nat) : dNext j f
 = P.d _ _ ≫ f (j + 1) j
参数：f : forall i j, P.X i ⟶ Q.X j；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem dNext_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) :
    dNext j f = P.d _ _ ≫ f (j + 1) j := by
  dsimp [dNext]
  have : (ComplexShape.up ℕ).next j = j + 1 := CochainComplex.next ℕ j
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.prevD_succ_cochainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：prevD_succ_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) (i : Nat) : prev
D (i + 1) f = f (i + 1) _ ≫ Q.d i (i + 1)
参数：f : forall i j, P.X i ⟶ Q.X j；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CochainComplex.prev_nat_succ`：prev_nat_succ (i : Nat) : (ComplexShape.up
 Nat).prev (i + 1) = i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem prevD_succ_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) :
    prevD (i + 1) f = f (i + 1) _ ≫ Q.d i (i + 1) := by
  dsimp [prevD]
  have : (ComplexShape.up ℕ).prev (i + 1) = i := CochainComplex.prev_nat_succ i
  congr 2

set_option backward.defeqAttrib.useBackward true in
-- This is not a simp lemma; the LHS already simplifies.
/-
**Homotopy.prevD_zero_cochainComplex** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
形式化陈述：prevD_zero_cochainComplex (f : forall i j, P.X i ⟶ Q.X j) : prevD 0 f = 0
参数：f : forall i j, P.X i ⟶ Q.X j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CochainComplex.prev_nat_zero`：prev_nat_zero : (ComplexShape.up Nat).prev
 0 = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem prevD_zero_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) : prevD 0 f = 0 := by
  dsimp [prevD]
  rw [Q.shape, comp_zero]
  rw [CochainComplex.prev_nat_zero]; dsimp; decide

variable (e : P ⟶ Q) (zero : P.X 1 ⟶ Q.X 0) (comm_zero : e.f 0 = P.d 0 1 ≫ zero)
  (one : P.X 2 ⟶ Q.X 1) (comm_one : e.f 1 = zero ≫ Q.d 0 1 + P.d 1 2 ≫ one)
  (succ :
    ∀ (n : ℕ)
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
/-
**Homotopy.mkCoinductiveAux** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkCoinductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agre
e.
They do in fact agree, and we then capture that at the type level (i.e. by const
ructing a homotopy)
in `mkCoinductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `xNext` and `xPrev`
,
which we do in `mkInductiveAux₂`.
-/
def mkCoinductiveAux₁ :
    ∀ n,
      Σ' (f : P.X (n + 1) ⟶ Q.X n) (f' : P.X (n + 2) ⟶ Q.X (n + 1)),
        e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'
  | 0 => ⟨zero, one, comm_one⟩
  | 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
  | n + 2 =>
    ⟨(mkCoinductiveAux₁ (n + 1)).2.1, (succ (n + 1) (mkCoinductiveAux₁ (n + 1))).1,
      (succ (n + 1) (mkCoinductiveAux₁ (n + 1))).2⟩

section

set_option backward.isDefEq.respectTransparency.types false in
/-- An auxiliary construction for `mkInductive`.
-/
/-
**Homotopy.mkCoinductiveAux** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkInductive`.
-/
def mkCoinductiveAux₂ :
    ∀ n, Σ' (f : P.X n ⟶ Q.xPrev n) (f' : P.xNext n ⟶ Q.X n), e.f n = f ≫ Q.dTo n + P.dFrom n ≫ f'
  | 0 => ⟨0, (P.xNextIso rfl).hom ≫ zero, by simpa using! comm_zero⟩
  | n + 1 =>
    let I := mkCoinductiveAux₁ e zero one comm_one succ n
    ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkCoinductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mkCoinductiveAux₂_zero :
    mkCoinductiveAux₂ e zero comm_zero one comm_one succ 0 =
      ⟨0, (P.xNextIso rfl).hom ≫ zero, by simpa using comm_zero⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkCoinductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mkCoinductiveAux₂_add_one (n) :
    mkCoinductiveAux₂ e zero comm_zero one comm_one succ (n + 1) =
      letI I := mkCoinductiveAux₁ e zero one comm_one succ n
      ⟨I.1 ≫ (Q.xPrevIso rfl).inv, (P.xNextIso rfl).hom ≫ I.2.1, by simpa using! I.2.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Homotopy.mkCoinductiveAux** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkCoinductiveAux₃ (i j : ℕ) (h : i + 1 = j) :
    (P.xNextIso h).inv ≫ (mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.1 =
      (mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).1 ≫ (Q.xPrevIso h).hom := by
  subst j
  rcases i with (_ | _ | i) <;> simp [mkCoinductiveAux₂]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A constructor for a `Homotopy e 0`, for `e` a chain map between `ℕ`-indexed cochain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
/-
**Homotopy.mkCoinductive** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：mkCoinductive : Homotopy e 0 where hom i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for a `Homotopy e 0`, for `e` a chain map between `ℕ`-indexed coch
ain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previou
s two components.
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

/-- A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
/-
**HomotopyEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {c : ComplexShap
e ι} → HomologicalComplex V c → HomologicalComplex V c → Type (max u_1 v)
参数：max u_1 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy equivalence between two chain complexes consists of a chain map each 
way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a P
rop.
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
/-- The morphism property on `HomologicalComplex V c` given by homotopy equivalences. -/
/-
**HomologicalComplex.homotopyEquivalences** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomologicalComplex.homotopyEquivalences : MorphismProperty (HomologicalCom
plex V c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property on `HomologicalComplex V c` given by homotopy equivalences
.
-/
def HomologicalComplex.homotopyEquivalences :
    MorphismProperty (HomologicalComplex V c) :=
  fun X Y f => ∃ (e : HomotopyEquiv X Y), e.hom = f

namespace HomotopyEquiv

variable {C D E : HomologicalComplex V c}

variable (C) in
/-- Any complex is homotopy equivalent to itself. -/
@[refl, simps]
/-
**HomotopyEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyEquiv`。
形式化陈述：refl : HomotopyEquiv C C where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any complex is homotopy equivalent to itself.
-/
def refl : HomotopyEquiv C C where
  hom := 𝟙 C
  inv := 𝟙 C
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)
/-
**HomotopyEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomotopyEquiv C C) :=
  ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm, simps]
/-
**HomotopyEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyEquiv`。
形式化陈述：symm (f : HomotopyEquiv C D) : HomotopyEquiv D C where hom
参数：f : HomotopyEquiv C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being homotopy equivalent is a symmetric relation.
-/
def symm (f : HomotopyEquiv C D) : HomotopyEquiv D C where
  hom := f.inv
  inv := f.hom
  homotopyHomInvId := f.homotopyInvHomId
  homotopyInvHomId := f.homotopyHomInvId

/-- Homotopy equivalence is a transitive relation. -/
@[trans, simps]
/-
**HomotopyEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyEquiv`。
形式化陈述：trans (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) : HomotopyEquiv C E 
where hom
参数：f : HomotopyEquiv C D；g : HomotopyEquiv D E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy equivalence is a transitive relation.
-/
def trans (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) :
    HomotopyEquiv C E where
  hom := f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  homotopyHomInvId := by simpa using
    ((g.homotopyHomInvId.compRightId f.inv).compLeft f.hom).trans f.homotopyHomInvId
  homotopyInvHomId := by simpa using
    ((f.homotopyInvHomId.compRightId g.hom).compLeft g.inv).trans g.homotopyInvHomId

/-- An isomorphism of complexes induces a homotopy equivalence. -/
/-
**HomotopyEquiv.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyEquiv`。
形式化陈述：ofIso {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : Compl
exShape ι} {C D : HomologicalComplex V c} (f : C ≅ D) : HomotopyEquiv C D
参数：f : C ≅ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of complexes induces a homotopy equivalence.
-/
def ofIso {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}
    {C D : HomologicalComplex V c} (f : C ≅ D) : HomotopyEquiv C D :=
  ⟨f.hom, f.inv, Homotopy.ofEq f.3, Homotopy.ofEq f.4⟩
/-
**HomotopyEquiv.homotopyEquivalences_hom** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyEqui
v`。
形式化陈述：homotopyEquivalences_hom (f : HomotopyEquiv C D) : homotopyEquivalences _ 
_ f.hom
参数：f : HomotopyEquiv C D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homotopyEquivalences_hom (f : HomotopyEquiv C D) :
    homotopyEquivalences _ _ f.hom := ⟨f, rfl⟩
/-
**HomotopyEquiv.homotopyEquivalences_inv** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyEqui
v`。
形式化陈述：homotopyEquivalences_inv (f : HomotopyEquiv C D) : homotopyEquivalences _ 
_ f.inv
参数：f : HomotopyEquiv C D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopyEquiv.homotopyEquivalences_hom`：homotopyEquivalences_hom (f : Ho
motopyEquiv C D) : homotopyEquivalences _ _ f.hom
-/
lemma homotopyEquivalences_inv (f : HomotopyEquiv C D) :
    homotopyEquivalences _ _ f.inv := f.symm.homotopyEquivalences_hom

/-- If `f` if a homotopy equivalence and `h` is a homotopy from `f.hom` to
a morphism `g`, then this is a homotopy equivalence whose `hom` field is `g`. -/
@[simps hom inv]
/-
**HomotopyEquiv.copy** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyEquiv`。
形式化陈述：copy (f : HomotopyEquiv C D) {g : C ⟶ D} (h : Homotopy f.hom g) : Homotopy
Equiv C D where hom
参数：f : HomotopyEquiv C D；h : Homotopy f.hom g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` if a homotopy equivalence and `h` is a homotopy from `f.hom` to
a morphism `g`, then this is a homotopy equivalence whose `hom` field is `g`.
-/
def copy (f : HomotopyEquiv C D) {g : C ⟶ D} (h : Homotopy f.hom g) :
    HomotopyEquiv C D where
  hom := g
  inv := f.inv
  homotopyHomInvId := (h.symm.compRight _).trans f.homotopyHomInvId
  homotopyInvHomId := (h.symm.compLeft _).trans f.homotopyInvHomId

end HomotopyEquiv

namespace HomologicalComplex

/-
**HomologicalComplex.homotopyEquivalences.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Ho
mologicalComplex.homotopyEquivalences`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} (f : C ⟶ D) [CategoryTheory.IsIso f],   HomologicalComplex.homotopyE
quivalences V c f
参数：f : C ⟶ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homotopyEquivalences.of_isIso (f : C ⟶ D) [IsIso f] : homotopyEquivalences _ _ f :=
  ⟨.ofIso (asIso f), rfl⟩
/-
**HomologicalComplex.homotopyEquivalences.of_homotopy** 是 Mathlib 中的一个定理，位于命名空间 
`HomologicalComplex.homotopyEquivalences`。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C D : HomologicalC
omplex V c} {f g : C ⟶ D},   HomologicalComplex.homotopyEquivalences V c f → ∀ (
hfg : Homotopy f g), HomologicalComplex.homotopyEquivalences V c g
参数：hfg : Homotopy f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopyEquiv.copy_hom`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTh
eory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexSh
ape ι} {C D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homotopyEquivalences.of_homotopy {f g : C ⟶ D} (h : homotopyEquivalences _ _ f)
    (hfg : Homotopy f g) :
    homotopyEquivalences _ _ g := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.copy hfg, by simp⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (homotopyEquivalences V c).IsMultiplicative where
  id_mem K := ⟨.refl _, rfl⟩
  comp_mem f g := by
    rintro ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.trans g, rfl⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (homotopyEquivalences V c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ _ ↦ .of_isIso _)

end HomologicalComplex

end

namespace CategoryTheory

variable {W : Type*} [Category* W] [Preadditive W]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An additive functor takes homotopies to homotopies. -/
@[simps]
/-
**CategoryTheory.Functor.mapHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{ι : Type u_1} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {c : ComplexShap
e ι} →           {C D : HomologicalComplex V c} →             {W : Type u_2} →  
             [inst_2 : CategoryTheory.Category.{v_1, u_2} W] →                 [
inst_3 : CategoryTheory.Preadditive W] →                   (F : CategoryTheory.F
unctor V W) →                     [inst_4 : F.Additive] →                       
{f g : C ⟶ D} →                         Homotopy f g → Homotopy ((F.mapHomologic
alComplex c).map f) ((F.mapHomologicalComplex c).map g)
参数：F : CategoryTheory.Functor V W；(F.mapHomologicalComplex c).map f；(F.mapHomolo
gicalComplex c).map g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
An additive functor takes homotopies to homotopies.
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
/-
**CategoryTheory.Functor.mapHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{ι : Type u_1} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {c : ComplexShap
e ι} →           {C D : HomologicalComplex V c} →             {W : Type u_2} →  
             [inst_2 : CategoryTheory.Category.{v_1, u_2} W] →                 [
inst_3 : CategoryTheory.Preadditive W] →                   (F : CategoryTheory.F
unctor V W) →                     [inst_4 : F.Additive] →                       
HomotopyEquiv C D →                         HomotopyEquiv ((F.mapHomologicalComp
lex c).obj C) ((F.mapHomologicalComplex c).obj D)
参数：F : CategoryTheory.Functor V W；(F.mapHomologicalComplex c).obj C；(F.mapHomolo
gicalComplex c).obj D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
An additive functor preserves homotopy equivalences.
-/
def Functor.mapHomotopyEquiv (F : V ⥤ W) [F.Additive] (h : HomotopyEquiv C D) :
    HomotopyEquiv ((F.mapHomologicalComplex c).obj C) ((F.mapHomologicalComplex c).obj D) where
  hom := (F.mapHomologicalComplex c).map h.hom
  inv := (F.mapHomologicalComplex c).map h.inv
  homotopyHomInvId := by
    rw [← (F.mapHomologicalComplex c).map_comp, ← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyHomInvId
  homotopyInvHomId := by
    rw [← (F.mapHomologicalComplex c).map_comp, ← (F.mapHomologicalComplex c).map_id]
    exact F.mapHomotopy h.homotopyInvHomId

end CategoryTheory

section

open HomologicalComplex CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}
  [DecidableRel c.Rel] {K L : HomologicalComplex C c} {f g : K ⟶ L}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A homotopy between morphisms of homological complexes `K ⟶ L` induces a homotopy
between morphisms of short complexes `K.sc i ⟶ L.sc i`. -/
/-
**Homotopy.toShortComplex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homotopy.toShortComplex (ho : Homotopy f g) (i : ι) : ShortComplex.Homotop
y ((shortComplexFunctor C c i).map f) ((shortComplexFunctor C c i).map g) where 
h₀
参数：ho : Homotopy f g；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.comm`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Cate
gory.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι} {C
 D …

--- 原说明 ---
A homotopy between morphisms of homological complexes `K ⟶ L` induces a homotopy
between morphisms of short complexes `K.sc i ⟶ L.sc i`.
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
      rw [L.shape _ _ h, comp_zero]
  g_h₃ := by
    split_ifs with h
    · simp
    · dsimp
      rw [K.shape _ _ h, zero_comp]
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
/-
**Homotopy.homologyMap_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.H
asHomology i] : homologyMap f i = homologyMap g i
参数：ho : Homotopy f g；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Homotopy.homologyMap_congr`：homologyMap_cong
r (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology] : homologyMap φ₁ = homo
logyMap φ₂
-/
lemma Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    homologyMap f i = homologyMap g i :=
  open scoped Classical in ShortComplex.Homotopy.homologyMap_congr (ho.toShortComplex i)

/-- The isomorphism in homology induced by a homotopy equivalence. -/
/-
**HomotopyEquiv.toHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι) [K.HasHomology
 i] [L.HasHomology i] : K.homology i ≅ L.homology i where hom
参数：h : HomotopyEquiv K L；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism in homology induced by a homotopy equivalence.
-/
noncomputable def HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] : K.homology i ≅ L.homology i where
  hom := homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

end

