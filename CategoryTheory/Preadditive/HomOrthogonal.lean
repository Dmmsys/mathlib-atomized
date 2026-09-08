/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Data.Set.Subsingleton

/-!
# Hom orthogonal families.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
theorem HomOrthogonal.equiv_of_iso (o : HomOrthogonal s) {f : α → ι} {g : β → ι}
    (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/

@[expose] public section


open Matrix CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.) -/
/-
**CategoryTheory.HomOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：HomOrthogonal {ι : Type*} (s : ι -> C) : Prop
参数：s : ι -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.)
-/
def HomOrthogonal {ι : Type*} (s : ι → C) : Prop :=
  Pairwise fun i j => Subsingleton (s i ⟶ s j)

namespace HomOrthogonal

variable {ι : Type*} {s : ι → C}

/-
**CategoryTheory.HomOrthogonal.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.HomOrthogonal`。
形式化陈述：eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i != j) 
(f : s i ⟶ s j) : f = 0
参数：o : HomOrthogonal s；w : i != j；f : s i ⟶ s j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
    f = 0 :=
  (o w).elim _ _

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

open scoped Classical in
/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps]
/-
**CategoryTheory.HomOrthogonal.matrixDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.HomOrthogonal`。
形式化陈述：matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite 
β] {f : α -> ι} {g : β -> ι} : ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ for
all i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) where toFun z i j k
参数：o : HomOrthogonal s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`.
-/
noncomputable def matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β]
    {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) where
  toFun z i j k :=
    eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          simp) ≫
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            simp)
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫ eqToHom (by simp [h]) else 0
  left_inv z := by
    ext j k
    simp only [biproduct.matrix_π, biproduct.ι_desc]
    split_ifs with h
    · simp
      rfl
    · symm
      apply o.eq_zero h
  right_inv z := by
    ext i ⟨j, w⟩ ⟨k, ⟨⟩⟩
    simp only [eqToHom_refl, biproduct.matrix_components, Category.id_comp]
    split_ifs with h
    · simp
    · exfalso
      exact h w.symm

end

section

variable [Preadditive C] [HasFiniteBiproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.matrixDecomposition` as an additive equivalence. -/
@[simps!]
/-
**CategoryTheory.HomOrthogonal.matrixDecompositionAddEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.HomOrthogonal`。
形式化陈述：matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Finite α] 
[Finite β] {f : α -> ι} {g : β -> ι} : ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b
)) ≃+ forall i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i))
参数：o : HomOrthogonal s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomOrthogonal.matrixDecomposition` as an additive equivalence.
-/
noncomputable def matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃+
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
@[simp]
/-
**CategoryTheory.HomOrthogonal.matrixDecomposition_id** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.HomOrthogonal`。
形式化陈述：matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Finite α] {f : α 
-> ι} (i : ι) : o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1
参数：o : HomOrthogonal s；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.HomOrthogonal.matrixDecomposition_apply`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {s : ι → C}   [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self`：bicone_ι_π_self {F : J -> C} (B :
 Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_ne`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] (f : J → C) [ins…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Finite α] {f : α → ι} (i : ι) :
    o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1 := by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Category.comp_id, Category.id_comp, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    simp
  · simp only [Subtype.mk.injEq] at h
    convert! comp_zero
    simpa using biproduct.ι_π_ne _ (Ne.symm h)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**CategoryTheory.HomOrthogonal.matrixDecomposition_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.HomOrthogonal`。
形式化陈述：matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Finite α] [
Fintype β] [Finite γ] {f : α -> ι} {g : β -> ι} {h : γ -> ι} (z : (⨁ fun a => s 
(f a)) ⟶ ⨁ fun b => s (g b)) (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i 
: ι) : o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i * o.matrixDec
omposition z i
参数：o : HomOrthogonal s；z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)；w : (⨁ fun 
b => s (g b)) ⟶ ⨁ fun c => s (h c)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.HomOrthogonal.matrixDecomposition_apply`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {s : ι → C}   [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biproduct.total`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {J : Type}   [in
st_2 : Fintype J] {f : J → …
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_congr_set`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : Fintype ι] (s : Set ι)   [inst_2 : DecidablePred fun x => x ∈ s
] (f : ι →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.HomOrthogonal.eq_zero`：eq_zero [HasZeroMorphisms C] (o : 
HomOrthogonal s) {i j : ι} (w : i != j) (f : s i ⟶ s j) : f = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β]
    [Finite γ] {f : α → ι} {g : β → ι} {h : γ → ι} (z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b))
    (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i : ι) :
    o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i * o.matrixDecomposition z i := by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_trans_assoc]
  conv_lhs => rw [← Category.id_comp w, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr_set
  · simp
  · intro b nm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at nm
    simp only [Category.assoc]
    convert! comp_zero
    convert! comp_zero
    convert! comp_zero
    convert! comp_zero
    simp only [o.eq_zero nm]

section

variable {R : Type*} [Semiring R] [Linear R C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.MatrixDecomposition` as an `R`-linear equivalence. -/
@[simps]
/-
**CategoryTheory.HomOrthogonal.matrixDecompositionLinearEquiv** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.HomOrthogonal`。
形式化陈述：matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Finite 
α] [Finite β] {f : α -> ι} {g : β -> ι} : ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (
g b)) ≃ₗ[R] forall i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i))
参数：o : HomOrthogonal s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomOrthogonal.MatrixDecomposition` as an `R`-linear equivalence.
-/
noncomputable def matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ₗ[R]
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

end

/-!
The hypothesis that `End (s i)` has invariant basis number is automatically satisfied
if `s i` is simple (as then `End (s i)` is a division ring).
-/


variable [∀ i, InvariantBasisNumber (End (s i))]

/-- Given a hom orthogonal family `s : ι → C`
for which each `End (s i)` is a ring with invariant basis number (e.g. if each `s i` is simple),
if two direct sums over `s` are isomorphic, then they have the same multiplicities.
-/
/-
**CategoryTheory.HomOrthogonal.equiv_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.HomOrthogonal`。
形式化陈述：equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f :
 α -> ι} {g : β -> ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : exists e
 : α ≃ β, forall a, g (e a) = f a
参数：o : HomOrthogonal s；i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Matrix.square_of_invertible`：Matrix.square_of_invertible (M : Matrix n m
 R) (N : Matrix m n R) (h : M * N = 1) (h' : N * M = 1) : Fintype.card n = Finty
pe.card m
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.HomOrthogonal.matrixDecomposition_comp`：matrixDecompositi
on_comp (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β] [Finite γ] {
f : α -> ι} {g : β -> ι} {h : γ -> ι} (z : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.HomOrthogonal.matrixDecomposition_id`：matrixDecomposition
_id (o : HomOrthogonal s) {α : Type} [Finite α] {f : α -> ι} (i : ι) : o.matrixD
ecomposition (𝟙 (⨁ fun a => s (f a))) i =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `Equiv.ofPreimageEquiv_map`：ofPreimageEquiv_map {α β γ} {f : α -> γ} {g :
 β -> γ} (e : forall c, f ⁻¹' {c} ≃ g ⁻¹' {c}) (a : α) : g (ofPreimageEquiv e a)
 = f a

--- 原说明 ---
Given a hom orthogonal family `s : ι → C`
for which each `End (s i)` is a ring with invariant basis number (e.g. if each `
s i` is simple),
if two direct sums over `s` are isomorphic, then they have the same multipliciti
es.
-/
theorem equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f : α → ι}
    {g : β → ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  refine ⟨Equiv.ofPreimageEquiv ?_, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  cases nonempty_fintype α; cases nonempty_fintype β
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrixDecomposition i.inv c) (o.matrixDecomposition i.hom c)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)

end

end HomOrthogonal

end CategoryTheory

