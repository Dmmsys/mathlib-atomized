/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Kan.HasKan
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.Tactic.TFAE

/-!
# Adjunctions as Kan extensions

We show that adjunctions are realized as Kan extensions or Kan lifts.

We also show that a left adjoint commutes with a left Kan extension. Under the assumption that
`IsLeftAdjoint h`, the isomorphism `f⁺ (g ≫ h) ≅ f⁺ g ≫ h` can be accessed by
`Lan.CommuteWith.lanCompIso f g h`.

## References

* [Riehl, *Category theory in context*, Proposition 6.5.2][riehl2017]

## TODO

At the moment, the results are stated for left Kan extensions and left Kan lifts. We can prove the
similar results for right Kan extensions and right Kan lifts.

-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

section LeftExtension

open LeftExtension

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Adjunction.isAbsoluteLeftKan` / `Adjunction.isAbsoluteLeftKan` 的定义

English:
definition Adjunction.isAbsoluteLeftKan
  signature: {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u)
  body: fun {x} h =>
  .mk (fun s => LeftExtension.homMk
(𝟙 _ otimes≫ u ◁ s.unit otimes≫ adj.counit ▷ s.extension otimes≫ 𝟙 _ : u ≫ h ⟶ s.extension)
      calc _
        _ = 𝟙 _ otimes≫ (adj.unit ▷ _ ≫ _ ◁ s.unit) otimes≫ f ◁ adj.counit ▷ s.extension otimes≫ 𝟙 _ := by
          dsimp only [whisker_extension

中文:
定义 伴随.isAbsoluteLeftKan
  签名: {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u)
  定义体: fun {x} h =>
  .mk (fun s => LeftExtension.homMk
(𝟙 _ otimes≫ u ◁ s.unit otimes≫ adj.counit ▷ s.extension otimes≫ 𝟙 _ : u ≫ h ⟶ s.extension)
      calc _
        _ = 𝟙 _ otimes≫ (adj.unit ▷ _ ≫ _ ◁ s.unit) otimes≫ f ◁ adj.counit ▷ s.extension otimes≫ 𝟙 _ := by
          dsimp only [whisker_extension
-/
def Adjunction.isAbsoluteLeftKan {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk u adj.unit) := fun {x} h =>
  .mk (fun s => LeftExtension.homMk
(𝟙 _ otimes≫ u ◁ s.unit otimes≫ adj.counit ▷ s.extension otimes≫ 𝟙 _ : u ≫ h ⟶ s.extension)
      calc _
        _ = 𝟙 _ otimes≫ (adj.unit ▷ _ ≫ _ ◁ s.unit) otimes≫ f ◁ adj.counit ▷ s.extension otimes≫ 𝟙 _ := by
          dsimp only [whisker_extension, StructuredArrow.mk_right, whisker_unit,
            StructuredArrow.mk_hom_eq_self]
          bicategory
        _ = 𝟙 _ otimes≫ s.unit otimes≫ leftZigzag adj.unit adj.counit ▷ s.extension otimes≫ 𝟙 _ := by
          rw [← whisker_exchange]; bicategory
        _ = s.unit := by
          rw [adj.left_triangle]; bicategory) <| by
    intro s τ₀
    ext
    /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
    let τ : u ≫ h ⟶ s.extension := τ₀.right
    have hτ : adj.unit ▷ h otimes≫ f ◁ τ = s.unit := by
      simpa [bicategoricalComp] using LeftExtension.w τ₀
    calc τ
      _ = 𝟙 _ otimes≫ rightZigzag adj.unit adj.counit ▷ h otimes≫ τ otimes≫ 𝟙 _ := by
        rw [adj.right_triangle]; bicategory
      _ = 𝟙 _ otimes≫ u ◁ adj.unit ▷ h otimes≫ (adj.counit ▷ _ ≫ _ ◁ τ) otimes≫ 𝟙 _ := by
        rw [rightZigzag]; bicategory
      _ = 𝟙 _ otimes≫ u ◁ (adj.unit ▷ h otimes≫ f ◁ τ) otimes≫ adj.counit ▷ s.extension otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
      _ = _ := by
        rw [hτ]; dsimp only [StructuredArrow.homMk_right]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `LeftExtension.IsKan.adjunction` / `LeftExtension.IsKan.adjunction` 的定义

English:
definition LeftExtension.IsKan.adjunction
  signature: {f : a ⟶ b} {t : LeftExtension f (𝟙 a)}
  body: let ε : t.extension ≫ f ⟶ 𝟙 b := H'.desc .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  have Hε : leftZigzag t.unit ε = (fun_ f).hom ≫ (ρ_ f).inv := by
simpa [leftZigzag, bicategoricalComp] using H'.fac .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  { unit := t.unit
    counit := ε
    left_triangle := Hε
    right_triangle 

中文:
定义 LeftExtension.IsKan.adjunction
  签名: {f : a ⟶ b} {t : LeftExtension f (𝟙 a)}
  定义体: let ε : t.extension ≫ f ⟶ 𝟙 b := H'.desc .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  have Hε : leftZigzag t.unit ε = (fun_ f).hom ≫ (ρ_ f).inv := by
simpa [leftZigzag, bicategoricalComp] using H'.fac .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  { unit := t.unit
    counit := ε
    left_triangle := Hε
    right_triangle 

Depends on / 依赖: H.hom_ext, bicategoricalComp, bicategory, cancel_epi, counit, extension, fun_, hom_ext, leftZigzag, left_triangle, otimes, rightZigzag, right_triangle, t.extension, t.unit
-/
def LeftExtension.IsKan.adjunction {f : a ⟶ b} {t : LeftExtension f (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker f)) :
      f ⊣ t.extension :=
let ε : t.extension ≫ f ⟶ 𝟙 b := H'.desc .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  have Hε : leftZigzag t.unit ε = (fun_ f).hom ≫ (ρ_ f).inv := by
simpa [leftZigzag, bicategoricalComp] using H'.fac .mk _ (fun_ f).hom ≫ (ρ_ f).inv
  { unit := t.unit
    counit := ε
    left_triangle := Hε
    right_triangle := by
      apply (cancel_epi (ρ_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ otimes≫ t.unit otimes≫ f ◁ rightZigzag t.unit ε otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ (t.unit ▷ _ ≫ _ ◁ t.unit) otimes≫ f ◁ ε ▷ t.extension otimes≫ 𝟙 _ := by
          rw [rightZigzag]; bicategory
        _ = 𝟙 _ otimes≫ t.unit otimes≫ (t.unit ▷ f otimes≫ f ◁ ε) ▷ t.extension otimes≫ 𝟙 _ := by
          rw [← whisker_exchange]; bicategory
        _ = _ := by
          rw [← leftZigzag]; rw [Hε]; bicategory }

/--
Definition of `LeftExtension.IsAbsKan.adjunction` / `LeftExtension.IsAbsKan.adjunction` 的定义

English:
definition LeftExtension.IsAbsKan.adjunction
  signature: {f : a ⟶ b} (t : LeftExtension f (𝟙 a)) (H : IsAbsKan t)
  body: H.isKan.adjunction (H f)

中文:
定义 LeftExtension.IsAbsKan.adjunction
  签名: {f : a ⟶ b} (t : LeftExtension f (𝟙 a)) (H : IsAbsKan t)
  定义体: H.isKan.adjunction (H f)

Depends on / 依赖: H.isKan.adjunction, adjunction
-/
def LeftExtension.IsAbsKan.adjunction {f : a ⟶ b} (t : LeftExtension f (𝟙 a)) (H : IsAbsKan t) :
    f ⊣ t.extension :=
  H.isKan.adjunction (H f)

/--
theorem `isLeftAdjoint_TFAE` / 定理 `isLeftAdjoint_TFAE`

English:
theorem isLeftAdjoint_TFAE
  given: (f : a ⟶ b)
  proof: by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanExtension (Adjunction.ofIsLeftAdjoint f).isAbsoluteLeftKan
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanIsKan f (𝟙 a)).adjunction Lan.CommuteWith.isKan f (𝟙 a) f
  tfae_finish

中文:
定理 isLeftAdjoint_TFAE
  条件: (f : a ⟶ b)
  证明: by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanExtension (Adjunction.ofIsLeftAdjoint f).isAbsoluteLeftKan
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanIsKan f (𝟙 a)).adjunction Lan.CommuteWith.isKan f (𝟙 a) f
  tfae_finish

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, CommuteWith, IsAbsKan, IsAbsKan.hasAbsLeftKanExtension, Lan.CommuteWith.isKan, adjunction, hasAbsLeftKanExtension, isAbsoluteLeftKan, lanIsKan, ofIsLeftAdjoint, tfae_finish, tfae_have
-/
theorem isLeftAdjoint_TFAE (f : a ⟶ b) :
    List.TFAE [
      IsLeftAdjoint f,
      HasAbsLeftKanExtension f (𝟙 a),
      exists _ : HasLeftKanExtension f (𝟙 a), Lan.CommuteWith f (𝟙 a) f] := by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanExtension (Adjunction.ofIsLeftAdjoint f).isAbsoluteLeftKan
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanIsKan f (𝟙 a)).adjunction Lan.CommuteWith.isKan f (𝟙 a) f
  tfae_finish

end LeftExtension

section LeftLift

open LeftLift

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Adjunction.isAbsoluteLeftKanLift` / `Adjunction.isAbsoluteLeftKanLift` 的定义

English:
definition Adjunction.isAbsoluteLeftKanLift
  signature: {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u)
  body: fun {x} h =>
  .mk (fun s => LeftLift.homMk
(𝟙 _ otimes≫ s.unit ▷ f otimes≫ s.lift ◁ adj.counit otimes≫ 𝟙 _ : h ≫ f ⟶ s.lift)
      calc _
      _ = 𝟙 _ otimes≫ (_ ◁ adj.unit ≫ s.unit ▷ _) otimes≫ s.lift ◁ adj.counit ▷ u otimes≫ 𝟙 _ := by
        dsimp only [whisker_lift, StructuredArrow.mk_right, w

中文:
定义 伴随.isAbsoluteLeftKanLift
  签名: {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u)
  定义体: fun {x} h =>
  .mk (fun s => LeftLift.homMk
(𝟙 _ otimes≫ s.unit ▷ f otimes≫ s.lift ◁ adj.counit otimes≫ 𝟙 _ : h ≫ f ⟶ s.lift)
      calc _
      _ = 𝟙 _ otimes≫ (_ ◁ adj.unit ≫ s.unit ▷ _) otimes≫ s.lift ◁ adj.counit ▷ u otimes≫ 𝟙 _ := by
        dsimp only [whisker_lift, StructuredArrow.mk_right, w

Depends on / 依赖: reflectsLimitsOfShapeOfCreatesLimitsOfShape
-/
def Adjunction.isAbsoluteLeftKanLift {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk f adj.unit) := fun {x} h =>
  .mk (fun s => LeftLift.homMk
(𝟙 _ otimes≫ s.unit ▷ f otimes≫ s.lift ◁ adj.counit otimes≫ 𝟙 _ : h ≫ f ⟶ s.lift)
      calc _
      _ = 𝟙 _ otimes≫ (_ ◁ adj.unit ≫ s.unit ▷ _) otimes≫ s.lift ◁ adj.counit ▷ u otimes≫ 𝟙 _ := by
        dsimp only [whisker_lift, StructuredArrow.mk_right, whisker_unit,
          StructuredArrow.mk_hom_eq_self]
        bicategory
      _ = s.unit otimes≫ s.lift ◁ (rightZigzag adj.unit adj.counit) otimes≫ 𝟙 _ := by
        rw [whisker_exchange]; rw [rightZigzag]; bicategory
      _ = s.unit := by
        rw [adj.right_triangle]; bicategory) <| by
      intro s τ₀
      ext
      /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
      let τ : h ≫ f ⟶ s.lift := τ₀.right
      have hτ : h ◁ adj.unit otimes≫ τ ▷ u = s.unit := by simpa [bicategoricalComp] using LeftLift.w τ₀
      calc τ
        _ = 𝟙 _ otimes≫ h ◁ leftZigzag adj.unit adj.counit otimes≫ τ otimes≫ 𝟙 _ := by
          rw [adj.left_triangle]; bicategory
        _ = 𝟙 _ otimes≫ h ◁ adj.unit ▷ f otimes≫ (_ ◁ adj.counit ≫ τ ▷ _) otimes≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
        _ = 𝟙 _ otimes≫ (h ◁ adj.unit otimes≫ τ ▷ u) ▷ f otimes≫ s.lift ◁ adj.counit otimes≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = _ := by
          rw [hτ]; dsimp only [StructuredArrow.homMk_right]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `LeftLift.IsKan.adjunction` / `LeftLift.IsKan.adjunction` 的定义

English:
definition LeftLift.IsKan.adjunction
  signature: {u : b ⟶ a} {t : LeftLift u (𝟙 a)}
  body: let ε : u ≫ t.lift ⟶ 𝟙 b := H'.desc .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  have Hε : rightZigzag t.unit ε = (ρ_ u).hom ≫ (fun_ u).inv := by
simpa [rightZigzag, bicategoricalComp] using H'.fac .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  { unit := t.unit
    counit := ε
    left_triangle := by
      apply (cancel_ep

中文:
定义 LeftLift.IsKan.adjunction
  签名: {u : b ⟶ a} {t : LeftLift u (𝟙 a)}
  定义体: let ε : u ≫ t.lift ⟶ 𝟙 b := H'.desc .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  have Hε : rightZigzag t.unit ε = (ρ_ u).hom ≫ (fun_ u).inv := by
simpa [rightZigzag, bicategoricalComp] using H'.fac .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  { unit := t.unit
    counit := ε
    left_triangle := by
      apply (cancel_ep

Depends on / 依赖: H.hom_ext, bicategoricalComp, bicategory, cancel_epi, counit, fun_, hom_ext, leftZigzag, left_triangle, otimes, reflectsLimitsOfCreatesLimits, rightZigzag, t.lift, t.unit
-/
def LeftLift.IsKan.adjunction {u : b ⟶ a} {t : LeftLift u (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker u)) :
      t.lift ⊣ u :=
let ε : u ≫ t.lift ⟶ 𝟙 b := H'.desc .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  have Hε : rightZigzag t.unit ε = (ρ_ u).hom ≫ (fun_ u).inv := by
simpa [rightZigzag, bicategoricalComp] using H'.fac .mk _ (ρ_ u).hom ≫ (fun_ u).inv
  { unit := t.unit
    counit := ε
    left_triangle := by
      apply (cancel_epi (fun_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ otimes≫ t.unit otimes≫ leftZigzag t.unit ε ▷ u otimes≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ otimes≫ (_ ◁ t.unit ≫ t.unit ▷ _) otimes≫ t.lift ◁ ε ▷ u otimes≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
        _ = 𝟙 _ otimes≫ t.unit otimes≫ t.lift ◁ (u ◁ t.unit otimes≫ ε ▷ u) otimes≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = _ := by
          rw [← rightZigzag]; rw [Hε]; bicategory
    right_triangle := Hε }

/--
Definition of `LeftLift.IsAbsKan.adjunction` / `LeftLift.IsAbsKan.adjunction` 的定义

English:
definition LeftLift.IsAbsKan.adjunction
  signature: {u : b ⟶ a} (t : LeftLift u (𝟙 a)) (H : IsAbsKan t)
  body: H.isKan.adjunction (H u)

中文:
定义 LeftLift.IsAbsKan.adjunction
  签名: {u : b ⟶ a} (t : LeftLift u (𝟙 a)) (H : IsAbsKan t)
  定义体: H.isKan.adjunction (H u)

Depends on / 依赖: H.isKan.adjunction, adjunction, reflectsColimitsOfShapeOfCreatesColimitsOfShape
-/
def LeftLift.IsAbsKan.adjunction {u : b ⟶ a} (t : LeftLift u (𝟙 a)) (H : IsAbsKan t) :
    t.lift ⊣ u :=
  H.isKan.adjunction (H u)

/--
theorem `isRightAdjoint_TFAE` / 定理 `isRightAdjoint_TFAE`

English:
theorem isRightAdjoint_TFAE
  given: (u : b ⟶ a)
  proof: by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanLift (Adjunction.ofIsRightAdjoint u).isAbsoluteLeftKanLift
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanLiftIsKan u (𝟙 a)).adjunction LanLift.CommuteWith.isKan u (𝟙 a) u
  tfae_finish

中文:
定理 isRightAdjoint_TFAE
  条件: (u : b ⟶ a)
  证明: by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanLift (Adjunction.ofIsRightAdjoint u).isAbsoluteLeftKanLift
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanLiftIsKan u (𝟙 a)).adjunction LanLift.CommuteWith.isKan u (𝟙 a) u
  tfae_finish

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, CommuteWith, IsAbsKan, IsAbsKan.hasAbsLeftKanLift, LanLift, LanLift.CommuteWith.isKan, adjunction, hasAbsLeftKanLift, isAbsoluteLeftKanLift, lanLiftIsKan, ofIsRightAdjoint, reflectsColimitsOfCreatesColimits, tfae_finish, tfae_have
-/
theorem isRightAdjoint_TFAE (u : b ⟶ a) :
    List.TFAE [
      IsRightAdjoint u,
      HasAbsLeftKanLift u (𝟙 a),
      exists _ : HasLeftKanLift u (𝟙 a), LanLift.CommuteWith u (𝟙 a) u] := by
  tfae_have 1 -> 2
  | h => IsAbsKan.hasAbsLeftKanLift (Adjunction.ofIsRightAdjoint u).isAbsoluteLeftKanLift
  tfae_have 2 -> 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 -> 1
| ⟨h, h'⟩ => .mk (lanLiftIsKan u (𝟙 a)).adjunction LanLift.CommuteWith.isKan u (𝟙 a) u
  tfae_finish

end LeftLift

namespace LeftExtension

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isKanOfWhiskerLeftAdjoint` / `isKanOfWhiskerLeftAdjoint` 的定义

English:
definition isKanOfWhiskerLeftAdjoint
  body: let η' := adj.unit
  let H' : LeftLift.IsAbsKan (.mk _ η') := adj.isAbsoluteLeftKanLift
  .mk (fun s =>
    let k := s.extension
    let θ := s.unit
let sτ := LeftExtension.mk _ 𝟙 _ otimes≫ g ◁ η' otimes≫ θ ▷ u otimes≫ 𝟙 _
    let τ : t.extension ⟶ k ≫ u := H.desc sτ
let sσ := LeftLift.mk _ (ρ_ _).h

中文:
定义 isKanOfWhiskerLeftAdjoint
  定义体: let η' := adj.unit
  let H' : LeftLift.IsAbsKan (.mk _ η') := adj.isAbsoluteLeftKanLift
  .mk (fun s =>
    let k := s.extension
    let θ := s.unit
let sτ := LeftExtension.mk _ 𝟙 _ otimes≫ g ◁ η' otimes≫ θ ▷ u otimes≫ 𝟙 _
    let τ : t.extension ⟶ k ≫ u := H.desc sτ
let sσ := LeftLift.mk _ (ρ_ _).h

Depends on / 依赖: H.desc, IsAbsKan, LeftExtension, LeftExtension.homMk, LeftExtension.mk, LeftLift, LeftLift.IsAbsKan, LeftLift.mk, adj.isAbsoluteLeftKanLift, adj.unit, bicategoricalComp, extension, hom_ext, isAbsoluteLeftKanLift, otimes, s.extension, s.unit, t.extension
-/
def isKanOfWhiskerLeftAdjoint
    {f : a ⟶ b} {g : a ⟶ c} {t : LeftExtension f g} (H : LeftExtension.IsKan t)
      {x : B} {h : c ⟶ x} {u : x ⟶ c} (adj : h ⊣ u) :
        LeftExtension.IsKan (t.whisker h) :=
  let η' := adj.unit
  let H' : LeftLift.IsAbsKan (.mk _ η') := adj.isAbsoluteLeftKanLift
  .mk (fun s =>
    let k := s.extension
    let θ := s.unit
let sτ := LeftExtension.mk _ 𝟙 _ otimes≫ g ◁ η' otimes≫ θ ▷ u otimes≫ 𝟙 _
    let τ : t.extension ⟶ k ≫ u := H.desc sτ
let sσ := LeftLift.mk _ (ρ_ _).hom ≫ τ
    let σ : t.extension ≫ h ⟶ k := H'.desc sσ
LeftExtension.homMk σ (H' g).hom_ext by
      have Hσ : t.extension ◁ η' otimes≫ σ ▷ u = 𝟙 _ otimes≫ τ := by
        simpa [bicategoricalComp] using (H' _).fac (.mk _ <| (ρ_ _).hom ≫ τ)
      dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
        StructuredArrow.mk_hom_eq_self, whisker_extension, whisker_unit]
      calc _
        _ = (g ◁ η' ≫ t.unit ▷ (h ≫ u)) otimes≫ f ◁ σ ▷ u otimes≫ 𝟙 _ := by
          bicategory
        _ = t.unit ▷ (𝟙 c) otimes≫ f ◁ (t.extension ◁ η' otimes≫ σ ▷ u) otimes≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = (ρ_ g).hom ≫ t.unit ≫ f ◁ H.desc sτ ≫ (α_ f s.extension u).inv := by
          rw [Hσ]
          dsimp only [τ]
          bicategory
        _ = _ := by
          rw [IsKan.fac_assoc]
          dsimp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self, sτ]
          bicategory) <| by
    intro s' τ₀'
    let τ' : t.extension ≫ h ⟶ s'.extension := τ₀'.right
    have Hτ' : t.unit ▷ h otimes≫ f ◁ τ' = s'.unit := by simpa [bicategoricalComp] using τ₀'.w
    ext
    apply (H' _).hom_ext
    dsimp only [StructuredArrow.homMk_right]
    rw [(H' _).fac]
    apply (cancel_epi (ρ_ _).inv).mp
    apply H.hom_ext
    dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
      StructuredArrow.mk_hom_eq_self]
    let σs' := LeftExtension.mk (s'.extension ≫ u)
      (𝟙 g otimes≫ g ◁ η' otimes≫ s'.unit ▷ u otimes≫ 𝟙 (f ≫ s'.extension ≫ u))
    calc _
      _ = 𝟙 _ otimes≫ (t.unit ▷ (𝟙 c) ≫ (f ≫ t.extension) ◁ η') otimes≫ f ◁ τ' ▷ u := by
        bicategory
      _ = 𝟙 g otimes≫ g ◁ η' otimes≫ (t.unit ▷ h otimes≫ f ◁ τ') ▷ u otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
      _ = t.unit ≫ f ◁ H.desc σs' := by
        rw [Hτ']; rw [IsKan.fac]
        dsimp only [StructuredArrow.mk_hom_eq_self, σs']
      _ = _ := by
        bicategory

instance {f : a ⟶ b} {g : a ⟶ c} {x : B} {h : c ⟶ x} [IsLeftAdjoint h] [HasLeftKanExtension f g] :
    Lan.CommuteWith f g h :=
  ⟨⟨isKanOfWhiskerLeftAdjoint (lanIsKan f g) (Adjunction.ofIsLeftAdjoint h)⟩⟩

end LeftExtension

end Bicategory

end CategoryTheory
