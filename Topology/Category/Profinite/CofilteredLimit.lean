/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_isClopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/

public section

namespace Profinite

open CategoryTheory Limits

universe u v

variable {J : Type v} [SmallCategory J] [IsCofiltered J] {F : J ⥤ Profinite.{max u v}} (C : Cone F)

set_option backward.isDefEq.respectTransparency false in
/-- If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
/-
**Profinite.exists_isClopen_of_cofiltered** 是 Mathlib 中的一个定理，位于命名空间 `Profinite`。
形式化陈述：exists_isClopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClop
en U) : exists (j : J) (V : Set (F.obj j)), IsClopen V ∧ U = C.π.app j ⁻¹' V
参数：hC : IsLimit C；hU : IsClopen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.isTopologicalBasis_cofiltered_limit`：isTopologicalBasis_cofiltere
d_limit (hC : IsLimit C) (T : forall j, Set (Set (F.obj j))) (hT : forall j, IsT
opologicalBasis (T j)) (univ : f…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `isTopologicalBasis_isClopen`：isTopologicalBasis_isClopen : IsTopological
Basis { s : Set X | IsClopen s }
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `isClopen_univ`：isClopen_univ : IsClopen (univ : Set X)
· 使用定理 `IsClopen.inter`：IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsC
lopen (s inter t)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`：∀ {α : Type u} [t : 
TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B →
 ∀ {u : Set α}, IsOpen u → ∃ S ⊆ B, u = …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `CategoryTheory.IsCofiltered.inf_objs_exists`：inf_objs_exists (O : Finset
 C) : exists S : C, forall {X}, X in O -> Nonempty (S ⟶ X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `isClopen_biUnion_finset`：isClopen_biUnion_finset {Y} {s : Finset Y} {f :
 Y -> Set X} (h : forall i in s, IsClopen <| f i) : IsClopen (⋃ i in s, f i)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` ar
ises from
a clopen set in one of the terms in the limit.
-/
theorem exists_isClopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)), IsClopen V ∧ U = C.π.app j ⁻¹' V := by
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := TopCat.isTopologicalBasis_cofiltered_limit.{u, v} (F ⋙ Profinite.toTopCat)
      (Profinite.toTopCat.mapCone C) (isLimitOfPreserves _ hC) (fun j => {W | IsClopen W}) ?_
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  rotate_left
  · intro i
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    apply isTopologicalBasis_isClopen
  · rintro i j f V (hV : IsClopen _)
    refine ⟨hV.1.preimage ?_, hV.2.preimage ?_⟩ <;> fun_prop
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.2
  clear hB
  let j : S → J := fun s => (hS s.2).choose
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.choose
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec
  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have hUo : ∀ (i : ↑S), IsOpen ((fun s ↦ (C.π.app (j s)) ⁻¹' V s) i) := by
    intro s
    exact (hV s).1.2.preimage (C.π.app (j s)).hom.hom.continuous
  have hsU : U ⊆ ⋃ (i : ↑S), (fun s ↦ C.π.app (j s) ⁻¹' V s) i := by
    dsimp only
    rw [h]
    rintro x ⟨T, hT, hx⟩
    refine ⟨_, ⟨⟨T, hT⟩, rfl⟩, ?_⟩
    dsimp only
    rwa [← (hV ⟨T, hT⟩).2]
  have := hU.1.isCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) hUo hsU
  -- We thus obtain a finite set `G : Finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G, hG⟩ := this
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  classical
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists (G.image j)
  let f : ∀ s ∈ G, j0 ⟶ j s := fun s hs => (hj0 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine ⟨j0, ⋃ (s : S) (_ : s ∈ G), W s, ?_, ?_⟩
  · apply isClopen_biUnion_finset
    intro s hs
    dsimp [W]
    rw [dif_pos hs]
    exact ⟨(hV s).1.1.preimage (F.map _).hom.hom.continuous,
      (hV s).1.2.preimage (F.map _).hom.hom.continuous⟩
  · ext x
    constructor
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion]
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      refine ⟨s, hs, ?_⟩
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, C.w]
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      rw [h]
      refine ⟨s.1, s.2, ?_⟩
      rw [(hV s).2]
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, C.w] at hx

set_option backward.isDefEq.respectTransparency false in
/-
**Profinite.exists_locallyConstant_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Profinite`
。
形式化陈述：exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt 
(Fin 2)) : exists (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (
C.π.app _).hom.hom
参数：hC : IsLimit C；f : LocallyConstant C.pt (Fin 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLocallyConstant.isClopen_fiber`：isClopen_fiber {f : X -> Y} (hf : IsLo
callyConstant f) (y : Y) : IsClopen { x | f x = y }
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
· 使用定理 `Profinite.exists_isClopen_of_cofiltered`：exists_isClopen_of_cofiltered {
U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) : exists (j : J) (V : Set (F.ob
j j)), IsClopen V ∧ U = C.π.a…
· 使用定理 `LocallyConstant.locallyConstant_eq_of_fiber_zero_eq`：locallyConstant_eq_
of_fiber_zero_eq {X : Type*} [TopologicalSpace X] (f g : LocallyConstant X (Fin 
2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocallyConstant.ofIsClopen_fiber_zero`：ofIsClopen_fiber_zero {X : Type*}
 [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)] (hU : IsClopen 
U) : ofIsClopen hU ⁻¹' ({0}…
-/
theorem exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _).hom.hom := by
  let U := f ⁻¹' {0}
  have hU : IsClopen U := f.isLocallyConstant.isClopen_fiber _
  obtain ⟨j, V, hV, h⟩ := exists_isClopen_of_cofiltered C hC hU
  classical
  use j, LocallyConstant.ofIsClopen hV
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  simp only [Fin.isValue, LocallyConstant.coe_comap, Set.preimage_comp,
    LocallyConstant.ofIsClopen_fiber_zero]
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**Profinite.exists_locallyConstant_finite_aux** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te`。
形式化陈述：exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C) 
(f : LocallyConstant C.pt α) : exists (j : J) (g : LocallyConstant (F.obj j) (α 
-> Fin 2)), (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.a
pp _).hom.hom
参数：hC : IsLimit C；f : LocallyConstant C.pt α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Profinite.exists_locallyConstant_fin_two`：exists_locallyConstant_fin_two
 (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) : exists (j : J) (g : Local
lyConstant (F.obj j) (Fin 2)),…
· 使用定理 `CategoryTheory.IsCofiltered.inf_objs_exists`：inf_objs_exists (O : Finset
 C) : exists S : C, forall {X}, X in O -> Nonempty (S ⟶ X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C)
    (f : LocallyConstant C.pt α) : ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _).hom.hom := by
  cases nonempty_fintype α
  let ι : α → α → Fin 2 := fun x y => if x = y then 0 else 1
  let ff := (f.map ι).flip
  have hff := fun a : α => exists_locallyConstant_fin_two _ hC (ff a)
  choose j g h using hff
  let G : Finset J := Finset.univ.image j
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists G
  have hj : ∀ a, j a ∈ (Finset.univ.image j : Finset J) := by grind
  let fs : ∀ a : α, j0 ⟶ j a := fun a => (hj0 (hj a)).some
  let gg : α → LocallyConstant (F.obj j0) (Fin 2) := fun a => (g a).comap (F.map (fs _)).hom.hom
  let ggg := LocallyConstant.unflip gg
  refine ⟨j0, ggg, ?_⟩
  have : f.map ι = LocallyConstant.unflip (f.map ι).flip := by simp
  rw [this]; clear this
  have :
    LocallyConstant.comap (C.π.app j0).hom.hom ggg =
      LocallyConstant.unflip (LocallyConstant.comap (C.π.app j0).hom.hom ggg).flip := by
    simp
  rw [this]; clear this
  congr 1
  ext1 a
  change ff a = _
  rw [h]
  dsimp
  ext1 x
  change _ = (g a) ((C.π.app j0 ≫ F.map (fs a)) x)
  rw [C.w]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Profinite.exists_locallyConstant_finite_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Pr
ofinite`。
形式化陈述：exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
 (hC : IsLimit C) (f : LocallyConstant C.pt α) : exists (j : J) (g : LocallyCons
tant (F.obj j) α), f = g.comap (C.π.app _).hom.hom
参数：hC : IsLimit C；f : LocallyConstant C.pt α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Profinite.exists_locallyConstant_finite_aux`：exists_locallyConstant_fini
te_aux {α : Type*} [Finite α] (hC : IsLimit C) (f : LocallyConstant C.pt α) : ex
ists (j : J) (g : LocallyConstant…
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
    (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _).hom.hom := by
  inhabit α
  obtain ⟨j, gg, h⟩ := exists_locallyConstant_finite_aux _ hC f
  classical
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.choose else default
  refine ⟨j, gg.map σ, ?_⟩
  ext x
  simp only [LocallyConstant.coe_comap, LocallyConstant.map_apply,
    Function.comp_apply]
  dsimp [σ]
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    rw [h]
    rfl
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  rw [dif_pos]
  swap
  · assumption
  apply_fun ι
  · rw [h2.choose_spec]
    exact h1
  · intro a b hh
    have hhh := congr_fun hh a
    dsimp [ι] at hhh
    rw [if_pos rfl] at hhh
    split_ifs at hhh with hh1
    · exact hh1.symm
    · exact False.elim (bot_ne_top hhh)

set_option backward.isDefEq.respectTransparency false in
/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
/-
**Profinite.exists_locallyConstant** 是 Mathlib 中的一个定理，位于命名空间 `Profinite`。
形式化陈述：exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C
.pt α) : exists (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app 
_).hom.hom
参数：hC : IsLimit C；f : LocallyConstant C.pt α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`：nonempty_limi
tCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v u}) [IsCofilteredOr
Empty J] [forall j : J, Nonempty (F.obj j)] [fo…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `DiscreteQuotient.proj_isLocallyConstant`：proj_isLocallyConstant : IsLoca
llyConstant S.proj
· 使用定理 `Profinite.exists_locallyConstant_finite_nonempty`：exists_locallyConstant
_finite_nonempty {α : Type*} [Finite α] [Nonempty α] (hC : IsLimit C) (f : Local
lyConstant C.pt α) : exists (j : J) (g…
· 使用定理 `DiscreteQuotient.instFiniteQuotientOfCompactSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] (S : DiscreteQuotient X) [CompactSpace X], Finite (Quoti
ent S.toSetoid)
· 使用定理 `IsLocallyConstant.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [
inst : TopologicalSpace X] {f : X → Y},   IsLocallyConstant f → ∀ (g : Y → Z), I
sLocallyCons…
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Any locally constant function from a cofiltered limit of profinite sets factors 
through
one of the components.
-/
theorem exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _).hom.hom := by
  let S := f.discreteQuotient
  let ff : S → α := f.lift
  cases isEmpty_or_nonempty S
  · suffices ∃ j, IsEmpty (F.obj j) by
      refine this.imp fun j hj => ?_
      refine ⟨⟨hj.elim, fun A => ?_⟩, ?_⟩
      · convert! isOpen_empty
        ext x
        exact hj.elim x
      · ext x
        exact hj.elim' (C.π.app j x)
    by_contra! h
    have : ∀ j : J, Nonempty ((F ⋙ Profinite.toTopCat).obj j) := h
    have : ∀ j : J, T2Space ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : T2Space (F.obj j))
    have : ∀ j : J, CompactSpace ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : CompactSpace (F.obj j))
    have cond := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u}
      (F ⋙ Profinite.toTopCat)
    suffices Nonempty C.pt from IsEmpty.false (S.proj this.some)
    let D := Profinite.toTopCat.mapCone C
    have hD : IsLimit D := isLimitOfPreserves Profinite.toTopCat hC
    have CD := (hD.conePointUniqueUpToIso (TopCat.limitConeIsLimit.{v, max u v} _)).inv
    exact cond.map CD
  · let f' : LocallyConstant C.pt S := ⟨S.proj, S.proj_isLocallyConstant⟩
    obtain ⟨j, g', hj⟩ := exists_locallyConstant_finite_nonempty _ hC f'
    refine ⟨j, ⟨ff ∘ g', g'.isLocallyConstant.comp _⟩, ?_⟩
    ext1 t
    apply_fun fun e => e t at hj
    dsimp at hj ⊢
    rw [← hj]
    rfl

end Profinite

