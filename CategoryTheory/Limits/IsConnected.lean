/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.HomCongr

/-!
# Colimits of connected index categories

This file proves two characterizations of connected categories by means of colimits.

## Characterization of connected categories by means of the unit-valued functor

First, it is proved that a category `C` is connected if and only if `colim F` is a singleton,
where `F : C ⥤ Type w` and `F.obj _ = PUnit` (for arbitrary `w`).

See `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit` for the proof of this characterization and
`constPUnitFunctor` for the definition of the constant functor used in the statement. A formulation
based on `IsColimit` instead of `colimit` is given in `isConnected_iff_isColimit_pUnitCocone`.

The `if` direction is also available directly in several formulations:
For connected index categories `C`, `PUnit.{w}` is a colimit of the `constPUnitFunctor`, where `w`
is arbitrary. See `instHasColimitConstPUnitFunctor`, `isColimitPUnitCocone` and
`colimitConstPUnitIsoPUnit`.

## Final functors preserve connectedness of categories (in both directions)

`isConnected_iff_of_final` proves that the domain of a final functor is connected if and only if
its codomain is connected.

## Tags

unit-valued, singleton, colimit
-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits.Types

variable (C : Type u) [Category.{v} C]

/-- The functor mapping every object to `PUnit`. -/
/-
**CategoryTheory.Limits.Types.constPUnitFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：constPUnitFunctor : C ⥤ Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor mapping every object to `PUnit`.
-/
def constPUnitFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}

/-- The cocone on `constPUnitFunctor` with cone point `PUnit`. -/
@[simps]
/-
**CategoryTheory.Limits.Types.pUnitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.Types`。
形式化陈述：pUnitCocone : Cocone (constPUnitFunctor.{w} C) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone on `constPUnitFunctor` with cone point `PUnit`.
-/
def pUnitCocone : Cocone (constPUnitFunctor.{w} C) where
  pt := PUnit
  ι := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` is connected, the cocone on `constPUnitFunctor` with cone point `PUnit` is a colimit
cocone. -/
/-
**CategoryTheory.Limits.Types.isColimitPUnitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Types`。
形式化陈述：isColimitPUnitCocone [IsConnected C] : IsColimit (pUnitCocone.{w} C) where
 desc s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
If `C` is connected, the cocone on `constPUnitFunctor` with cone point `PUnit` i
s a colimit
cocone.
-/
noncomputable def isColimitPUnitCocone [IsConnected C] : IsColimit (pUnitCocone.{w} C) where
  desc s := s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    refine constant_of_preserves_morphisms (α := s.pt)
      (fun (k : C) ↦ s.ι.app k PUnit.unit) ?_ Classical.ofNonempty j
    intro X Y f
    exact ConcreteCategory.congr_hom (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]
/-
**CategoryTheory.Limits.Types.instHasColimitConstPUnitFunctor** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：instHasColimitConstPUnitFunctor [IsConnected C] : HasColimit (constPUnitFu
nctor.{w} C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasColimitConstPUnitFunctor [IsConnected C] : HasColimit (constPUnitFunctor.{w} C) :=
  ⟨_, isColimitPUnitCocone _⟩
/-
**CategoryTheory.Limits.Types.instSubsingletonColimitPUnit** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：instSubsingletonColimitPUnit [IsPreconnected C] [HasColimit (constPUnitFun
ctor.{w} C)] : Subsingleton colimit (constPUnitFunctor.{w} C) where allEq a b
参数：constPUnitFunctor.{w} C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms`：constant_of_preserves_mo
rphisms [IsPreconnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_
 : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J)…
· 使用定理 `CategoryTheory.Limits.Types.colimit_sound`：colimit_sound {j j' : J} {x :
 F.obj j} {x' : F.obj j'} (f : j ⟶ j') (w : F.map f x = x') : colimit.ι F j x = 
colimit.ι F j' x'
-/
instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (constPUnitFunctor.{w} C)] :
    Subsingleton <| colimit (constPUnitFunctor.{w} C) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
/-
**CategoryTheory.Limits.Types.colimitConstPUnitIsoPUnit** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Types`。
形式化陈述：colimitConstPUnitIsoPUnit [IsConnected C] : colimit (constPUnitFunctor.{w}
 C) ≅ PUnit.{w + 1}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a connected index category, the colimit of the constant unit-valued functo
r is `PUnit`.
-/
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (constPUnitFunctor.{w} C) ≅ PUnit.{w + 1} :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

/-- Let `F` be a `Type`-valued functor. If two elements `a : F c` and `b : F d` represent the
same element of `colimit F`, then `c` and `d` are related by a `Zigzag`. -/
/-
**CategoryTheory.Limits.Types.zigzag_of_eqvGen_colimitTypeRel** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：zigzag_of_eqvGen_colimitTypeRel (F : C ⥤ Type w) (c d : Σ j, F.obj j) (h :
 Relation.EqvGen F.ColimitTypeRel c d) : Zigzag c.1 d.1
参数：F : C ⥤ Type w；c d : Σ j, F.obj j；h : Relation.EqvGen F.ColimitTypeRel c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Zigzag.refl`：∀ {J : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} J] (X : J), CategoryTheory.Zigzag X X
· 使用定理 `CategoryTheory.Zigzag.symm`：∀ {J : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.Zigz
ag j₂ j₁
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…

--- 原说明 ---
Let `F` be a `Type`-valued functor. If two elements `a : F c` and `b : F d` repr
esent the
same element of `colimit F`, then `c` and `d` are related by a `Zigzag`.
-/
theorem zigzag_of_eqvGen_colimitTypeRel (F : C ⥤ Type w) (c d : Σ j, F.obj j)
    (h : Relation.EqvGen F.ColimitTypeRel c d) : Zigzag c.1 d.1 := by
  induction h with
  | rel _ _ h => exact Zigzag.of_hom <| Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An index category is connected iff the colimit of the constant singleton-valued functor is a
singleton. -/
/-
**CategoryTheory.Limits.Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUni
t** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isConnected_iff_colimit_constPUnitFunctor_iso_pUnit [HasColimit (constPUni
tFunctor.{w} C)] : IsConnected C ↔ Nonempty (colimit (constPUnitFunctor.{w} C) ≅
 PUnit)
参数：constPUnitFunctor.{w} C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.nonempty_of_nonempty_colimit`：nonempty_of_no
nempty_colimit {F : J ⥤ Type u} [HasColimit F] : Nonempty (colimit F) -> Nonempt
y J
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Limits.Types.zigzag_of_eqvGen_colimitTypeRel`：zigzag_of_e
qvGen_colimitTypeRel (F : C ⥤ Type w) (c d : Σ j, F.obj j) (h : Relation.EqvGen 
F.ColimitTypeRel c d) : Zigzag c.1 d.1
· 使用定理 `CategoryTheory.Limits.Types.colimit_eq`：colimit_eq {j j' : J} {x : F.obj
 j} {x' : F.obj j'} (w : colimit.ι F j x = colimit.ι F j' x') : Relation.EqvGen 
F.ColimitTypeRel ⟨j, x⟩ ⟨j',…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
An index category is connected iff the colimit of the constant singleton-valued 
functor is a
singleton.
-/
theorem isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
    [HasColimit (constPUnitFunctor.{w} C)] :
    IsConnected C ↔ Nonempty (colimit (constPUnitFunctor.{w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_colimitTypeRel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl
/-
**CategoryTheory.Limits.Types.isConnected_iff_isColimit_pUnitCocone** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isConnected_iff_isColimit_pUnitCocone : IsConnected C ↔ Nonempty (IsColimi
t (pUnitCocone.{w} C))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.isConnected_iff_colimit_constPUnitFunctor_is
o_pUnit`：isConnected_iff_colimit_constPUnitFunctor_iso_pUnit [HasColimit (constP
UnitFunctor.{w} C)] : IsConnected C ↔ Nonempty (colimit (constPUnitFu…
-/
theorem isConnected_iff_isColimit_pUnitCocone :
    IsConnected C ↔ Nonempty (IsColimit (pUnitCocone.{w} C)) := by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩

end Limits.Types

namespace Functor

open Limits.Types

universe v₂ u₂

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/-- The domain of a final functor is connected if and only if its codomain is connected. -/
/-
**CategoryTheory.Functor.isConnected_iff_of_final** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：isConnected_iff_of_final (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnect
ed D
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isConnected_iff_colimit_constPUnitFunctor_is
o_pUnit`：isConnected_iff_colimit_constPUnitFunctor_iso_pUnit [HasColimit (constP
UnitFunctor.{w} C)] : IsConnected C ↔ Nonempty (colimit (constPUnitFu…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β

--- 原说明 ---
The domain of a final functor is connected if and only if its codomain is connec
ted.
-/
theorem isConnected_iff_of_final (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D := by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C,
    isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
  exact Equiv.nonempty_congr <| Iso.isoCongrLeft <|
    CategoryTheory.Functor.Final.colimitIso F <| constPUnitFunctor.{max u v u₂ v₂} D

/-- The domain of an initial functor is connected if and only if its codomain is connected. -/
/-
**CategoryTheory.Functor.isConnected_iff_of_initial** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：isConnected_iff_of_initial (F : C ⥤ D) [F.Initial] : IsConnected C ↔ IsCon
nected D
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isConnected_op_iff_isConnected`：isConnected_op_iff_isConn
ected : IsConnected Jᵒᵖ ↔ IsConnected J
· 使用定理 `CategoryTheory.Functor.isConnected_iff_of_final`：isConnected_iff_of_fina
l (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D

--- 原说明 ---
The domain of an initial functor is connected if and only if its codomain is con
nected.
-/
theorem isConnected_iff_of_initial (F : C ⥤ D) [F.Initial] : IsConnected C ↔ IsConnected D := by
  rw [← isConnected_op_iff_isConnected C, ← isConnected_op_iff_isConnected D]
  exact isConnected_iff_of_final F.op

end Functor

section

variable (C : Type*) [Category* C]

/-- Prove that a category is connected by supplying an explicit initial object. -/
/-
**CategoryTheory.isConnected_of_isInitial** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isConnected_of_isInitial {x : C} (h : Limits.IsInitial x) : IsConnected C
参数：h : Limits.IsInitial x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_zigzag`：isConnected_of_zigzag [Nonempty J]
 (h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ 
:: l) (List.cons_ne_nil _ …
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Zag.symm`：∀ {J : Type u₁} [inst : CategoryTheory.Category
.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zag j₂ j₁
· 使用定理 `CategoryTheory.Zag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zag j₁ j₂

--- 原说明 ---
Prove that a category is connected by supplying an explicit initial object.
-/
lemma isConnected_of_isInitial {x : C} (h : Limits.IsInitial x) : IsConnected C := by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
  exact ⟨Zag.symm <| Zag.of_hom <| h.to _, Zag.of_hom <| h.to _⟩

/-- Prove that a category is connected by supplying an explicit terminal object. -/
/-
**CategoryTheory.isConnected_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isConnected_of_isTerminal {x : C} (h : Limits.IsTerminal x) : IsConnected 
C
参数：h : Limits.IsTerminal x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_zigzag`：isConnected_of_zigzag [Nonempty J]
 (h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ 
:: l) (List.cons_ne_nil _ …
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Zag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zag j₁ j₂
· 使用定理 `CategoryTheory.Zag.symm`：∀ {J : Type u₁} [inst : CategoryTheory.Category
.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zag j₂ j₁

--- 原说明 ---
Prove that a category is connected by supplying an explicit terminal object.
-/
lemma isConnected_of_isTerminal {x : C} (h : Limits.IsTerminal x) : IsConnected C := by
  let : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
  exact ⟨Zag.of_hom <| h.from _, Zag.symm <| Zag.of_hom <| h.from _⟩

-- note : it seems making the following two as instances breaks things, so these are lemmas.
/-
**CategoryTheory.isConnected_of_hasInitial** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isConnected_of_hasInitial [Limits.HasInitial C] : IsConnected C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isConnected_of_isInitial`：isConnected_of_isInitial {x : C
} (h : Limits.IsInitial x) : IsConnected C
-/
lemma isConnected_of_hasInitial [Limits.HasInitial C] : IsConnected C :=
  isConnected_of_isInitial C Limits.initialIsInitial
/-
**CategoryTheory.isConnected_of_hasTerminal** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isConnected_of_hasTerminal [Limits.HasTerminal C] : IsConnected C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isConnected_of_isTerminal`：isConnected_of_isTerminal {x :
 C} (h : Limits.IsTerminal x) : IsConnected C
-/
lemma isConnected_of_hasTerminal [Limits.HasTerminal C] : IsConnected C :=
  isConnected_of_isTerminal C Limits.terminalIsTerminal

end

end CategoryTheory

