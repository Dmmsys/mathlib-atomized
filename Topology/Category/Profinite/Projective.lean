/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Profinite sets have enough projectives

In this file we show that `Profinite` has enough projectives.

## Main results

Let `X` be a profinite set.

* `Profinite.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `Profinite.projectivePresentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

-/

@[expose] public section


noncomputable section

universe u v w

open CategoryTheory Function

namespace Profinite

/-
**Profinite.projective_ultrafilter** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：projective_ultrafilter (X : Type u) : Projective (of <| Ultrafilter X) whe
re factors {Y Z} f g hg
参数：X : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instTotallyDisconnectedSpaceUltrafilter`：∀ {α : Type u}, TotallyDisconne
ctedSpace (Ultrafilter α)
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.epi_iff_surjective`：epi_iff_surjective {X Y : Profinite.{u}} (
f : X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `continuous_ultrafilter_extend`：continuous_ultrafilter_extend (f : α -> γ
) : Continuous (Ultrafilter.extend f)
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用引理 `CategoryTheory.ConcreteCategory.coe_ext`：coe_ext {X Y : C} {f g : X ⟶ Y}
 (h : ⇑(hom f) = ⇑(hom g)) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `denseRange_pure`：denseRange_pure : DenseRange (pure : α -> Ultrafilter α
)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用引理 `ultrafilter_extend_extends`：ultrafilter_extend_extends (f : α -> γ) : Ul
trafilter.extend f ∘ pure = f
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
instance projective_ultrafilter (X : Type u) : Projective (of <| Ultrafilter X) where
  factors {Y Z} f g hg := by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    let t : X → Y := g' ∘ f ∘ (pure : X → Ultrafilter X)
    let h : Ultrafilter X → Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use CompHausLike.ofHom _ ⟨h, hh⟩
    apply ConcreteCategory.coe_ext
    simp only [h]
    convert! denseRange_pure.equalizer (g.hom.hom.continuous.comp hh) f.hom.hom.continuous _
    have : g.hom ∘ g' = id := hg'.comp_eq_id
    rw [comp_assoc, ultrafilter_extend_extends, ← comp_assoc, this, id_comp]
    rfl

/-- For any profinite `X`, the natural map `Ultrafilter X → X` is a projective presentation. -/
/-
**Profinite.projectivePresentation** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：projectivePresentation (X : Profinite.{u}) : ProjectivePresentation X wher
e p
参数：X : Profinite.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any profinite `X`, the natural map `Ultrafilter X → X` is a projective prese
ntation.
-/
def projectivePresentation (X : Profinite.{u}) : ProjectivePresentation X where
  p := of <| Ultrafilter X
  f := CompHausLike.ofHom _ ⟨_, continuous_ultrafilter_extend id⟩
  projective := Profinite.projective_ultrafilter X
  epi := ConcreteCategory.epi_of_surjective _ fun x =>
    ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩
/-
**Profinite.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnoughProjectives Profinite.{u} where presentation X := ⟨projectivePresentation X⟩

end Profinite

