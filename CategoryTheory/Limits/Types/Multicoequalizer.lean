/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.MultiequalizerPullback
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Types.Set
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# Multicoequalizers in the category of types

Given `J : MultispanShape`, `d : MultispanIndex J (Type u)` and
`c : d.multispan.CoconeTypes`, we obtain a lemma `isMulticoequalizer_iff`
which gives a criteria for `c` to be a colimit (i.e. a multicoequalizer):
it restates in a more explicit manner the injectivity and surjectivity
conditions for the map `d.multispan.descColimitType c : d.multispan.ColimitType → c.pt`.

We deduce a definition `Set.isColimitOfMulticoequalizerDiagram` which shows
that given `X : Type u`, a `MulticoequalizerDiagram` in `Set X` gives
a multicoequalizer in the category of types.

-/

@[expose] public section

universe w w' u

namespace CategoryTheory.Functor.CoconeTypes

open Limits

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.CoconeTypes.isMulticoequalizer_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.CoconeTypes`。
形式化陈述：isMulticoequalizer_iff {J : MultispanShape.{w, w'}} {d : MultispanIndex J 
(Type u)} (c : d.multispan.CoconeTypes) : c.IsColimit ↔ (forall (i₁ i₂ : J.R) (x
₁ : d.right i₁) (x₂ : d.right i₂), c.ι (.right i₁) x₁ = c.ι (.right i₂) x₂ -> d.
multispan.ιColimitType (.right i₁) x₁ = d.multispan.ιColimitType (.right i₂) x₂)
 ∧ (forall (x : c.pt), exists (i : J.R) (a : d.right i), c.ι (.right i) a = x)
参数：Type u；c : d.multispan.CoconeTypes。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.ιColimitType_map`：ιColimitType_map {j j' : J} (f 
: j ⟶ j') (x : F.obj j) : F.ιColimitType j' (F.map f x) = F.ιColimitType j x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.bijective`：∀ {J : Type u} [
inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)
} {c : F.CoconeTypes},   c.IsColimit → Funct…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isMulticoequalizer_iff {J : MultispanShape.{w, w'}} {d : MultispanIndex J (Type u)}
    (c : d.multispan.CoconeTypes) :
    c.IsColimit ↔
      (∀ (i₁ i₂ : J.R) (x₁ : d.right i₁) (x₂ : d.right i₂),
        c.ι (.right i₁) x₁ = c.ι (.right i₂) x₂ →
          d.multispan.ιColimitType (.right i₁) x₁ = d.multispan.ιColimitType (.right i₂) x₂) ∧
      (∀ (x : c.pt), ∃ (i : J.R) (a : d.right i), c.ι (.right i) a = x) := by
  have (x : d.multispan.ColimitType) :
      ∃ (i : J.R) (a : d.right i), d.multispan.ιColimitType (.right i) a = x := by
    obtain ⟨(l | r), z, rfl⟩ := d.multispan.ιColimitType_jointly_surjective x
    · exact ⟨J.fst l, d.multispan.map (WalkingMultispan.Hom.fst l) z, by rw [ιColimitType_map]⟩
    · exact ⟨r, z, by simp⟩
  constructor
  · intro hc
    refine ⟨fun i₁ i₂ x₁ x₂ h ↦ ?_, ?_⟩
    · simp only [← descColimitType_ιColimitType_apply] at h
      exact hc.bijective.1 h
    · intro x
      obtain ⟨y, rfl⟩ := hc.bijective.2 x
      obtain ⟨i, z, rfl⟩ := this y
      exact ⟨i, z, by simp⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x₁ x₂ h ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨i₁, a₁, rfl⟩ := this x₁
      obtain ⟨i₂, a₂, rfl⟩ := this x₂
      exact h₁ _ _ _ _ h
    · obtain ⟨i, y, rfl⟩ := h₂ x
      exact ⟨d.multispan.ιColimitType (.right i) y, rfl⟩

end CategoryTheory.Functor.CoconeTypes

open CompleteLattice CategoryTheory Limits

namespace CategoryTheory.Limits.Types

variable {X : Type u} {ι : Type w} {A : Set X} {U : ι → Set X} {V : ι → ι → Set X}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `X : Type u`, `A : Set X`, `U : ι → Set X` and `V : ι → ι → Set X` such
that `MulticoequalizerDiagram A U V` holds, then in the category of types,
`A` is the multicoequalizer of the `U i`s along the `V i j`s. -/
/-
**CategoryTheory.Limits.Types.isColimitOfMulticoequalizerDiagram** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isColimitOfMulticoequalizerDiagram (c : MulticoequalizerDiagram A U V) : I
sColimit (c.multicofork.map Set.functorToTypes)
参数：c : MulticoequalizerDiagram A U V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : Type u`, `A : Set X`, `U : ι → Set X` and `V : ι → ι → Set X` such
that `MulticoequalizerDiagram A U V` holds, then in the category of types,
`A` is the multicoequalizer of the `U i`s along the `V i j`s.
-/
noncomputable def isColimitOfMulticoequalizerDiagram
    (c : MulticoequalizerDiagram A U V) :
    IsColimit (c.multicofork.map Set.functorToTypes) := by
  let e := (c.multispanIndex.map Set.functorToTypes).multispan
  apply _root_.Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit,
    Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨fun i₁ i₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · dsimp at i₁ i₂ h₁ h₂
    obtain rfl : x₁ = x₂ := by simpa using h
    have eq₁ := e.ιColimitType_map (WalkingMultispan.Hom.fst (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.eq_inf]; exact ⟨h₁, h₂⟩⟩
    have eq₂ := e.ιColimitType_map (WalkingMultispan.Hom.snd (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.eq_inf]; exact ⟨h₁, h₂⟩⟩
    dsimp [e] at eq₁ eq₂
    rw [eq₁, eq₂]
  · simp only [MulticoequalizerDiagram.multicofork_pt, ← c.iSup_eq,
      Set.iSup_eq_iUnion, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X : Type u`, `A : Set X`, `U : ι → Set X` and `V : ι → ι → Set X` such
that `MulticoequalizerDiagram A U V` holds, then in the category of types,
`A` is the multicoequalizer of the `U i`s along the `V i j`s. In this version,
we assume `ι` has a linear order, which allows to consider only the `V i j`
for which `i < j`. -/
/-
**CategoryTheory.Limits.Types.isColimitOfMulticoequalizerDiagram'** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：isColimitOfMulticoequalizerDiagram' [LinearOrder ι] (c : MulticoequalizerD
iagram A U V) : IsColimit (c.multicofork.toLinearOrder.map Set.functorToTypes)
参数：c : MulticoequalizerDiagram A U V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `X : Type u`, `A : Set X`, `U : ι → Set X` and `V : ι → ι → Set X` such
that `MulticoequalizerDiagram A U V` holds, then in the category of types,
`A` is the multicoequalizer of the `U i`s along the `V i j`s. In this version,
we assume `ι` has a linear order, which allows to consider only the `V i j`
for which `i < j`.
-/
noncomputable def isColimitOfMulticoequalizerDiagram' [LinearOrder ι]
    (c : MulticoequalizerDiagram A U V) :
    IsColimit (c.multicofork.toLinearOrder.map Set.functorToTypes) :=
  Multicofork.isColimitToLinearOrder _ (isColimitOfMulticoequalizerDiagram c)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        dsimp
        rw [c.eq_inf, c.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

/-- A bicartesian square in the lattice `Set X` gives a pushout diagram in the
category of types. -/
/-
**CategoryTheory.Limits.Types.isPushout_of_bicartSq** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.Types`。
形式化陈述：isPushout_of_bicartSq {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃
 S₄) : IsPushout (Set.functorToTypes.map (homOfLE h.le₁₂)) (Set.functorToTypes.m
ap (homOfLE h.le₁₃)) (Set.functorToTypes.map (homOfLE h.le₂₄)) (Set.functorToTyp
es.map (homOfLE h.le₃₄))
参数：h : Lattice.BicartSq S₁ S₂ S₃ S₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout`：isPushout (hc : I
sColimit c) : IsPushout (I.fst default) (I.snd default) (c.π (J.fst default)) (c
.π (J.snd default)) where w
· 使用引理 `Lattice.BicartSq.multicoequalizerDiagram`：Lattice.BicartSq.multicoequali
zerDiagram {T : Type u} [CompleteLattice T] {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x
₃ x₄) : CompleteLattice.Multic…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
A bicartesian square in the lattice `Set X` gives a pushout diagram in the
category of types.
-/
lemma isPushout_of_bicartSq {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃ S₄) :
    IsPushout (Set.functorToTypes.map (homOfLE h.le₁₂))
      (Set.functorToTypes.map (homOfLE h.le₁₃))
      (Set.functorToTypes.map (homOfLE h.le₂₄))
      (Set.functorToTypes.map (homOfLE h.le₃₄)) :=
  Multicofork.IsColimit.isPushout _ (by ext (_ | _) <;> tauto) (by tauto)
    (isColimitOfMulticoequalizerDiagram' h.multicoequalizerDiagram)

end CategoryTheory.Limits.Types

