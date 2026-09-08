/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.IsUniquelyCodimOneFace

/-!
# Pairings

In this file, we introduce the definition of a pairing for a subcomplex `A`
of a simplicial set `X`, following the ideas by Sean Moss,
*Another approach to the Kan-Quillen model structure*, who gave a
complete combinatorial characterization of strong (inner) anodyne extensions.
Strong (inner) anodyne extensions are transfinite compositions of pushouts of coproducts
of (inner) horn inclusions, i.e. this is similar to (inner) anodyne extensions but
without the stability property under retracts.

A pairing for `A` consists in the data of a partition of the nondegenerate
simplices of `X` not in `A` into type (I) simplices and type (II) simplices,
and of a bijection between the types of type (I) and type (II) simplices.
Indeed, the main observation is that when we attach a simplex along a horn
inclusion, exactly two nondegenerate simplices are added: this simplex,
and the unique face which is not in the image of the horn. The former shall be
considered as of type (I) and the latter as type (II).

We say that a pairing is *regular* (typeclass `Pairing.IsRegular`) when
- it is proper (`Pairing.IsProper`), i.e. any type (II) simplex is uniquely
  a face of the corresponding type (I) simplex.
- a certain ancestrality relation is well founded.

When these conditions are satisfied, the inclusion `A.ι : A ⟶ X` is
a strong anodyne extension (TODO @joelriou), and the converse is also true
(if `A.ι` is a strong anodyne extension, then there is a regular pairing for `A` (TODO)).

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- A pairing for a subcomplex `A` of a simplicial set `X` consists of a partition
of the nondegenerate simplices of `X` not in `A` in two types (I) and (II) of simplices,
and a bijection between the type (II) simplices and the type (I) simplices.
See the introduction of the file
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean`. -/
/-
**SSet.Subcomplex.Pairing** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} → X.Subcomplex → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pairing for a subcomplex `A` of a simplicial set `X` consists of a partition
of the nondegenerate simplices of `X` not in `A` in two types (I) and (II) of si
mplices,
and a bijection between the type (II) simplices and the type (I) simplices.
See the introduction of the file
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean`.
-/
structure Pairing where
  /-- the set of type (I) simplices -/
  I : Set A.N
  /-- the set of type (II) simplices -/
  II : Set A.N
  inter : I ∩ II = ∅
  union : I ∪ II = Set.univ
  /-- a bijection from the type (II) simplices to the type (I) simplices -/
  p : II ≃ I

namespace Pairing

variable {A} (P : A.Pairing)

/-- A pairing is proper when each type (II) simplex
is uniquely a `1`-codimensional face of the corresponding (I)
simplex. -/
/-
**SSet.Subcomplex.Pairing.IsProper** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex.
Pairing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.Pairing → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pairing is proper when each type (II) simplex
is uniquely a `1`-codimensional face of the corresponding (I)
simplex.
-/
class IsProper where
  isUniquelyCodimOneFace (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
/-
**SSet.Subcomplex.Pairing.isUniquelyCodimOneFace** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing`。
形式化陈述：isUniquelyCodimOneFace [P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace 
x.1.toS (P.p x).1.toS
参数：x : P.II。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.IsProper.isUniquelyCodimOneFace`：∀ {X : _root_.S
Set} {A : X.Subcomplex} {P : A.Pairing} [self : P.IsProper] (x : ↑P.II),   (↑x).
IsUniquelyCodimOneFace (↑(P.p x)).toS
-/
lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS :=
  IsProper.isUniquelyCodimOneFace x

@[simp]
/-
**SSet.Subcomplex.Pairing.dim_p** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairi
ng`。
形式化陈述：dim_p [P.IsProper] (x : P.II) : (P.p x).1.dim = x.1.dim + 1
参数：x : P.II。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
-/
lemma dim_p [P.IsProper] (x : P.II) :
    (P.p x).1.dim = x.1.dim + 1 :=
  (P.isUniquelyCodimOneFace x).dim_eq

/-- The condition that a pairing only involves inner horns. -/
/-
**SSet.Subcomplex.Pairing.IsInner** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex.P
airing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → (P : A.Pairing) → [P.IsProper] → 
Prop
参数：P : A.Pairing。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a pairing only involves inner horns.
-/
class IsInner [P.IsProper] : Prop where
  ne_zero (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ 0
  ne_last (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ Fin.last _

/-- The ancestrality relation on type (II) simplices. -/
/-
**SSet.Subcomplex.Pairing.AncestralRel** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomple
x.Pairing`。
形式化陈述：AncestralRel (x y : P.II) : Prop
参数：x y : P.II。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ancestrality relation on type (II) simplices.
-/
def AncestralRel (x y : P.II) : Prop :=
  x ≠ y ∧ x.1 < (P.p y).1

variable {P} in
/-
**SSet.Subcomplex.Pairing.AncestralRel.dim_le** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Su
bcomplex.Pairing.AncestralRel`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} {P : A.Pairing} [P.IsProper] {x y :
 ↑P.II},   P.AncestralRel x y → (↑x).dim ≤ (↑y).dim
参数：↑x；↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.dim_eq`：dim_eq : y.dim = x.dim + 1
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用引理 `SSet.N.dim_lt_of_lt`：dim_lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.di
m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma AncestralRel.dim_le [P.IsProper] {x y : P.II} (hxy : P.AncestralRel x y) :
    x.1.dim ≤ y.1.dim := by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using
    SSet.N.dim_lt_of_lt hxy.2

/-- A proper pairing is regular when the ancestrality relation
is well founded. -/
/-
**SSet.Subcomplex.Pairing.IsRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomplex
.Pairing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.Pairing → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper pairing is regular when the ancestrality relation
is well founded.
-/
class IsRegular extends P.IsProper where
  wf : WellFounded P.AncestralRel

section

variable [P.IsRegular]

/-
**SSet.Subcomplex.Pairing.wf** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing`
。
形式化陈述：wf : WellFounded P.AncestralRel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.IsRegular.wf`：∀ {X : _root_.SSet} {A : X.Subcomp
lex} {P : A.Pairing} [self : P.IsRegular], WellFounded P.AncestralRel
-/
lemma wf : WellFounded P.AncestralRel := IsRegular.wf
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsWellFounded _ P.AncestralRel where
  wf := P.wf

end

/-
**SSet.Subcomplex.Pairing.exists_or** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.P
airing`。
形式化陈述：exists_or (x : A.N) : exists (y : P.II), x = y ∨ x = P.p y
参数：x : A.N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Subcomplex.Pairing.union`：∀ {X : _root_.SSet} {A : X.Subcomplex} (s
elf : A.Pairing), self.I ∪ self.II = Set.univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma exists_or (x : A.N) :
    ∃ (y : P.II), x = y ∨ x = P.p y := by
  have := Set.mem_univ x
  rw [← P.union, Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩
/-
**SSet.Subcomplex.Pairing.ne** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing`
。
形式化陈述：ne (x : P.I) (y : P.II) : x.1 != y.1
参数：x : P.I；y : P.II。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Subcomplex.Pairing.inter`：∀ {X : _root_.SSet} {A : X.Subcomplex} (s
elf : A.Pairing), self.I ∩ self.II = ∅
-/
lemma ne (x : P.I) (y : P.II) :
    x.1 ≠ y.1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rintro rfl
  have : x ∈ P.I ∩ P.II := ⟨hx, hy⟩
  simp [P.inter] at this
/-
**SSet.Subcomplex.Pairing.le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing`
。
形式化陈述：le [P.IsProper] (x : P.II) : x.1 <= (P.p x).1
参数：x : P.II。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.le`：le : x <= y
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
-/
lemma le [P.IsProper] (x : P.II) :
    x.1 ≤ (P.p x).1 :=
  (P.isUniquelyCodimOneFace x).le
/-
**SSet.Subcomplex.Pairing.lt** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairing`
。
形式化陈述：lt [P.IsProper] (x : P.II) : x.1 < (P.p x).1
参数：x : P.II。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用引理 `SSet.Subcomplex.Pairing.le`：le [P.IsProper] (x : P.II) : x.1 <= (P.p x).
1
· 使用引理 `SSet.Subcomplex.Pairing.ne`：ne (x : P.I) (y : P.II) : x.1 != y.1
-/
lemma lt [P.IsProper] (x : P.II) :
    x.1 < (P.p x).1 :=
  lt_of_le_of_ne' (P.le x) (P.ne _ _)

variable {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B)

/-- Given an isomorphism `Y ≅ X` of simplicial sets, a pairing `P` of a subcomplex
`A` of `X`, this is a pairing for a subcomplex `B` of `Y` if `A.preimage e.hom = B`. -/
@[simps I II]
/-
**SSet.Subcomplex.Pairing.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pairi
ng`。
形式化陈述：ofIso : B.Pairing where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Given an isomorphism `Y ≅ X` of simplicial sets, a pairing `P` of a subcomplex
`A` of `X`, this is a pairing for a subcomplex `B` of `Y` if `A.preimage e.hom =
 B`.
-/
def ofIso : B.Pairing where
  I := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.I
  II := Subcomplex.N.orderIsoOfIso e hA ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := ((Subcomplex.N.orderIsoOfIso e hA).subtypeEquiv (by simp)).trans
    (P.p.trans ((Subcomplex.N.orderIsoOfIso e hA).symm.subtypeEquiv (by simp)))

/-- A unification hint for the type (I) simplices of `Pairing.ofIso`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
    {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B) where
  ⊢ (P.ofIso e hA).I ≟ (N.orderIsoOfIso e hA) ⁻¹' P.I

/-- A unification hint for the type (II) simplices of `Pairing.ofIso`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
    {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B) where
  ⊢ (P.ofIso e hA).II ≟ (N.orderIsoOfIso e hA) ⁻¹' P.II

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**SSet.Subcomplex.Pairing.ofIso_p** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pai
ring`。
形式化陈述：ofIso_p (x : P.II) : dsimp% (P.ofIso e hA).p ⟨(Subcomplex.N.orderIsoOfIso 
e hA).symm x, by simp⟩ = ⟨(Subcomplex.N.orderIsoOfIso e hA).symm (P.p x), by sim
p⟩
参数：x : P.II。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofIso_p (x : P.II) :
    dsimp% (P.ofIso e hA).p ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩ =
    ⟨(Subcomplex.N.orderIsoOfIso e hA).symm (P.p x), by simp⟩ := by
  let e' := Subcomplex.N.orderIsoOfIso e hA
  ext
  change e'.symm (P.p ⟨e' (e'.symm x), _⟩) = e'.symm (P.p x)
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.Pairing.ofIso_ancestralRel_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing`。
形式化陈述：ofIso_ancestralRel_iff (x y : P.II) : (P.ofIso e hA).AncestralRel ⟨(Subcom
plex.N.orderIsoOfIso e hA).symm x, by simp⟩ ⟨(Subcomplex.N.orderIsoOfIso e hA).s
ymm y, by simp⟩ ↔ P.AncestralRel x y
参数：x y : P.II。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `SSet.Subcomplex.Pairing.ofIso_p`：ofIso_p (x : P.II) : dsimp% (P.ofIso e 
hA).p ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩ = ⟨(Subcomplex.N.order
IsoOfIso e hA).symm (…
-/
lemma ofIso_ancestralRel_iff (x y : P.II) :
    (P.ofIso e hA).AncestralRel
      ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩
      ⟨(Subcomplex.N.orderIsoOfIso e hA).symm y, by simp⟩ ↔
    P.AncestralRel x y :=
  and_congr (not_congr (by aesop)) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsProper] : (P.ofIso e hA).IsProper where
  isUniquelyCodimOneFace := by
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective x
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hx
    simp only [ofIso_II, ofIso_I, dsimp% P.ofIso_p e hA ⟨x, hx⟩]
    exact (P.isUniquelyCodimOneFace ⟨x, hx⟩).of_iso e.symm
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsRegular] : (P.ofIso e hA).IsRegular where
  wf := by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n ↦ ⟨_, (f n).2⟩, fun n ↦ ?_⟩
    simpa [← P.ofIso_ancestralRel_iff e hA] using hf n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SSet.Subcomplex.Pairing.ofIso_index** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex
.Pairing`。
形式化陈述：ofIso_index (x : P.II) {d : Nat} (hd : x.1.dim = d) [P.IsProper] : ((P.ofI
so e hA).isUniquelyCodimOneFace ⟨(N.orderIsoOfIso e hA).symm x, by simp⟩).index 
hd = (isUniquelyCodimOneFace P x).index hd
参数：x : P.II；hd : x.1.dim = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.isUniquelyCodimOneFace`：isUniquelyCodimOneFace [
P.IsProper] (x : P.II) : S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS
· 使用定理 `SSet.Subcomplex.Pairing.instIsProperOfIso`：∀ {X : _root_.SSet} {A : X.Su
bcomplex} (P : A.Pairing) {Y : _root_.SSet} {B : Y.Subcomplex} (e : Y ≅ X)   (hA
 : A.preimage e.hom = B) [P.IsP…
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.of_iso`：of_iso {Y : SSet.{u}} (e : X ≅ Y) 
: (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.sim
plex))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.S.IsUniquelyCodimOneFace.index_of_iso`：index_of_iso {Y : SSet.{u}} 
(e : X ≅ Y) {d : Nat} (hd : x.dim = d) : (hxy.of_iso e).index hd = hxy.index hd
· 使用引理 `SSet.Subcomplex.Pairing.ofIso_p`：ofIso_p (x : P.II) : dsimp% (P.ofIso e 
hA).p ⟨(Subcomplex.N.orderIsoOfIso e hA).symm x, by simp⟩ = ⟨(Subcomplex.N.order
IsoOfIso e hA).symm (…
-/
lemma ofIso_index (x : P.II) {d : ℕ} (hd : x.1.dim = d) [P.IsProper] :
    ((P.ofIso e hA).isUniquelyCodimOneFace ⟨(N.orderIsoOfIso e hA).symm x, by simp⟩).index hd =
      (isUniquelyCodimOneFace P x).index hd := by
  rw [← (P.isUniquelyCodimOneFace x).index_of_iso e.symm hd]
  congr
  rw [P.ofIso_p e hA x]
  rfl
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsProper] [P.IsInner] : (P.ofIso e hA).IsInner where
  ne_zero := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_zero ⟨a, hb⟩ hd
  ne_last := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsInner.ne_last ⟨a, hb⟩ hd

end Pairing

end SSet.Subcomplex

