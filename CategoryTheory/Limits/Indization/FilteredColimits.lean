/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Colimit
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Indization.IndObject
public import Mathlib.Logic.Small.Set

/-!
# Ind-objects are closed under filtered colimits

We show that if `F : I ⥤ Cᵒᵖ ⥤ Type v` is a functor such that `I` is small and filtered and
`F.obj i` is an ind-object for all `i`, then `colimit F` is also an ind-object.

Our proof is a slight variant of the proof given in Kashiwara-Schapira.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Theorem 6.1.8
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.CostructuredArrow CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

namespace IndizationClosedUnderFilteredColimitsAux

variable {I : Type v} [SmallCategory I] (F : I ⥤ Cᵒᵖ ⥤ Type v)


section Interchange

/-!
We start by stating the key interchange property `exists_nonempty_limit_obj_of_isColimit`. It
consists of pulling out a colimit out of a hom functor and interchanging a filtered colimit with
a finite limit.
-/

variable {J : Type v} [SmallCategory J] [FinCategory J]

variable (G : J ⥤ CostructuredArrow yoneda (colimit F))

-- We introduce notation for the functor `J ⥤ Over (colimit F)` induced by `G`.
local notation "𝒢" => Functor.op G ⋙ Functor.op (toOver yoneda (colimit F))

variable {K : Type v} [SmallCategory K] (H : K ⥤ Over (colimit F))

/--
Definition of `compYonedaColimitIsoColimitCompYoneda` / `compYonedaColimitIsoColimitCompYoneda` 的定义

English:
definition compYonedaColimitIsoColimitCompYoneda
  signature: :
  body: calc
  𝒢 ⋙ yoneda.obj (colimit H) ≅ 𝒢 ⋙ colimit (H ⋙ yoneda) :=
        isoWhiskerLeft G.op (toOverCompYonedaColimit H)
  _ ≅ 𝒢 ⋙ (H ⋙ yoneda).flip ⋙ colim := isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip ⋙ colim := Iso.refl _
  _ ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := (colimitIsoFlipCompColim _).symm

中文:
定义 compYonedaColimitIsoColimitCompYoneda
  签名: :
  定义体: calc
  𝒢 ⋙ yoneda.obj (colimit H) ≅ 𝒢 ⋙ colimit (H ⋙ yoneda) :=
        isoWhiskerLeft G.op (toOverCompYonedaColimit H)
  _ ≅ 𝒢 ⋙ (H ⋙ yoneda).flip ⋙ colim := isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip ⋙ colim := Iso.refl _
  _ ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := (colimitIsoFlipCompColim _).symm
-/
noncomputable def compYonedaColimitIsoColimitCompYoneda :
    𝒢 ⋙ yoneda.obj (colimit H) ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := calc
  𝒢 ⋙ yoneda.obj (colimit H) ≅ 𝒢 ⋙ colimit (H ⋙ yoneda) :=
        isoWhiskerLeft G.op (toOverCompYonedaColimit H)
  _ ≅ 𝒢 ⋙ (H ⋙ yoneda).flip ⋙ colim := isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip ⋙ colim := Iso.refl _
  _ ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := (colimitIsoFlipCompColim _).symm

/--
theorem `exists_nonempty_limit_obj_of_colimit` / 定理 `exists_nonempty_limit_obj_of_colimit`

English:
theorem exists_nonempty_limit_obj_of_colimit
  statement: [IsFiltered K]
  proof: by
  obtain ⟨t⟩ := h
  let t₂ := limMap (compYonedaColimitIsoColimitCompYoneda F G H).hom t
  let t₃ := (colimitLimitIso (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip k).hom y
  let y := flipCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) k
  exact (lim.mapIso y).hom z

中文:
定理 存在_nonempty_limit_obj_of_colimit
  结论: [是Filtered K]
  证明: by
  obtain ⟨t⟩ := h
  let t₂ := limMap (compYonedaColimitIsoColimitCompYoneda F G H).hom t
  let t₃ := (colimitLimitIso (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip k).hom y
  let y := flipCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) k
  exact (lim.mapIso y).hom z

Depends on / 依赖: Types.jointly_surjective, colimitLimitIso, compYonedaColimitIsoColimitCompYoneda, flipCompEvaluation, jointly_surjective, lim.mapIso, limMap, limitObjIsoLimitCompEvaluation, mapIso, whiskeringLeft, yoneda
-/
theorem exists_nonempty_limit_obj_of_colimit [IsFiltered K]
    (h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj (colimit H))) :
    exists k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.obj k)) := by
  obtain ⟨t⟩ := h
  let t₂ := limMap (compYonedaColimitIsoColimitCompYoneda F G H).hom t
  let t₃ := (colimitLimitIso (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip k).hom y
  let y := flipCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) k
  exact (lim.mapIso y).hom z

/--
theorem `exists_nonempty_limit_obj_of_isColimit` / 定理 `exists_nonempty_limit_obj_of_isColimit`

English:
theorem exists_nonempty_limit_obj_of_isColimit
  statement: [IsFiltered K] {c : Cocone H} (hc : IsColimit c)
  proof: by
  refine exists_nonempty_limit_obj_of_colimit F G H ?_
  suffices T ≅ colimit H from Nonempty.map (lim.map (whiskerLeft 𝒢 (yoneda.map this.hom))) h
  refine hT.symm ≪≫ IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

中文:
定理 存在_nonempty_limit_obj_of_isColimit
  结论: [是Filtered K] {c : 余锥 H} (hc : 是余极限 c)
  证明: by
  refine exists_nonempty_limit_obj_of_colimit F G H ?_
  suffices T ≅ colimit H from Nonempty.map (lim.map (whiskerLeft 𝒢 (yoneda.map this.hom))) h
  refine hT.symm ≪≫ IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, Nonempty, Nonempty.map, coconePointUniqueUpToIso, colimit, colimit.isColimit, exists_nonempty_limit_obj_of_colimit, hT.symm, isColimit, lim.map, this.hom, whiskerLeft, yoneda, yoneda.map
-/
theorem exists_nonempty_limit_obj_of_isColimit [IsFiltered K] {c : Cocone H} (hc : IsColimit c)
    (T : Over (colimit F)) (hT : c.pt ≅ T)
    (h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj T)) :
    exists k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.obj k)) := by
  refine exists_nonempty_limit_obj_of_colimit F G H ?_
  suffices T ≅ colimit H from Nonempty.map (lim.map (whiskerLeft 𝒢 (yoneda.map this.hom))) h
  refine hT.symm ≪≫ IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

end Interchange

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isFiltered` / 定理 `isFiltered`

English:
theorem isFiltered
  given: [IsFiltered I] (hF : forall i, IsIndObject (F.obj i))
  proof: by
  -- It suffices to show that for any functor `G : J ⥤ CostructuredArrow yoneda (colimit F)` with
  -- `J` finite there is some `X` such that the set
  -- `lim Hom_{CostructuredArrow yoneda (colimit F)}(G·, X)` is nonempty.
  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  -- We begin by remarking that `lim Hom_{Over (colimit F)}(yG·, 𝟙 (colimit F))` is nonempty,
  -- simply because `𝟙 (colimit F)` is the terminal object. Here `y` is the functor
  -- `CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` induced by `yoneda`.
  have h₁ : Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver _ _).op ⋙
      yoneda.obj (Over.mk (𝟙 (colimit F))))) :=
    ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) (by simp)⟩
  -- `𝟙 (colimit F)` is the colimit of the diagram in `Over (colimit F)` given by the arrows of
  -- the form `Fi ⟶ colimit F`. Thus, pulling the colimit out of the hom functor and commuting
  -- the finite limit with the filtered colimit, we obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, 𝟙 (colimit F)) ≅`
  -- `colim_i lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i)`, and so we find `i` such that
  -- the limit is non-empty.
  obtain ⟨i, hi⟩ := exists_nonempty_limit_obj_of_isColimit F G _
    (colimit.isColimitToOver F) _ (Iso.refl _) h₁
  -- `F.obj i` is a small filtered colimit of representables, say of the functor `H : K ⥤ C`, so
  -- `𝟙 (F.obj i)` is the colimit of the arrows of the form `yHk ⟶ Fi` in `Over Fi`.
  -- Then `colimit.ι F i` is the colimit of the arrows of the form
  -- `H.obj F ⟶ F.obj i ⟶ colimit F` in `Over (colimit F)`.
  obtain ⟨⟨P⟩⟩ := hF i
  let hc : IsColimit ((Over.map (colimit.ι F i)).mapCocone P.cocone.toOver) :=
    isColimitOfPreserves (Over.map _) (Over.isColimitToOver P.coconeIsColimit)
  -- Again, we pull the colimit out of the hom functor and commute limit and colimit to obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i) ≅`
  -- `colim_k lim_j Hom_{Over (colimit F)}(yGj, yHk)`, and so we find `k` such that the limit
  -- is non-empty.
  obtain ⟨k, hk⟩ : exists k, Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
      yoneda.obj ((CostructuredArrow.toOver yoneda (colimit F)).obj <|
(CostructuredArrow.pre P.F yoneda (colimit F)).obj
(map (colimit.ι F i)).obj mk _))) :=
    exists_nonempty_limit_obj_of_isColimit F G _ hc _ (Iso.refl _) hi
  have htO : (CostructuredArrow.toOver yoneda (colimit F)).FullyFaithful := .ofFullyFaithful _
  -- Since the inclusion `y : CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` is fully
  -- faithful, `lim_j Hom_{Over (colimit F)}(yGj, yHk) ≅`
  -- `lim_j Hom_{CostructuredArrow yoneda (colimit F)}(Gj, Hk)` and so `Hk` is the object we're
  -- looking for.
  let q := fun X => isoWhiskerLeft _ (uliftYonedaIsoYoneda.symm.app _) ≪≫ htO.homNatIso X
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) hk
  exact ⟨_, ⟨((preservesLimitIso uliftFunctor.{max u v, v} _).inv t').down⟩⟩

中文:
定理 isFiltered
  条件: [是Filtered I] (hF : 对任意 i, 是IndObject (F.obj i))
  证明: by
  -- It suffices to show that for any functor `G : J ⥤ CostructuredArrow yoneda (colimit F)` with
  -- `J` finite there is some `X` such that the set
  -- `lim Hom_{CostructuredArrow yoneda (colimit F)}(G·, X)` is nonempty.
  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  -- We begin by remarking that `lim Hom_{Over (colimit F)}(yG·, 𝟙 (colimit F))` is nonempty,
  -- simply because `𝟙 (colimit F)` is the terminal object. Here `y` is the functor
  -- `CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` induced by `yoneda`.
  have h₁ : Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver _ _).op ⋙
      yoneda.obj (Over.mk (𝟙 (colimit F))))) :=
    ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) (by simp)⟩
  -- `𝟙 (colimit F)` is the colimit of the diagram in `Over (colimit F)` given by the arrows of
  -- the form `Fi ⟶ colimit F`. Thus, pulling the colimit out of the hom functor and commuting
  -- the finite limit with the filtered colimit, we obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, 𝟙 (colimit F)) ≅`
  -- `colim_i lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i)`, and so we find `i` such that
  -- the limit is non-empty.
  obtain ⟨i, hi⟩ := exists_nonempty_limit_obj_of_isColimit F G _
    (colimit.isColimitToOver F) _ (Iso.refl _) h₁
  -- `F.obj i` is a small filtered colimit of representables, say of the functor `H : K ⥤ C`, so
  -- `𝟙 (F.obj i)` is the colimit of the arrows of the form `yHk ⟶ Fi` in `Over Fi`.
  -- Then `colimit.ι F i` is the colimit of the arrows of the form
  -- `H.obj F ⟶ F.obj i ⟶ colimit F` in `Over (colimit F)`.
  obtain ⟨⟨P⟩⟩ := hF i
  let hc : IsColimit ((Over.map (colimit.ι F i)).mapCocone P.cocone.toOver) :=
    isColimitOfPreserves (Over.map _) (Over.isColimitToOver P.coconeIsColimit)
  -- Again, we pull the colimit out of the hom functor and commute limit and colimit to obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i) ≅`
  -- `colim_k lim_j Hom_{Over (colimit F)}(yGj, yHk)`, and so we find `k` such that the limit
  -- is non-empty.
  obtain ⟨k, hk⟩ : exists k, Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
      yoneda.obj ((CostructuredArrow.toOver yoneda (colimit F)).obj <|
(CostructuredArrow.pre P.F yoneda (colimit F)).obj
(map (colimit.ι F i)).obj mk _))) :=
    exists_nonempty_limit_obj_of_isColimit F G _ hc _ (Iso.refl _) hi
  have htO : (CostructuredArrow.toOver yoneda (colimit F)).FullyFaithful := .ofFullyFaithful _
  -- Since the inclusion `y : CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` is fully
  -- faithful, `lim_j Hom_{Over (colimit F)}(yGj, yHk) ≅`
  -- `lim_j Hom_{CostructuredArrow yoneda (colimit F)}(Gj, Hk)` and so `Hk` is the object we're
  -- looking for.
  let q := fun X => isoWhiskerLeft _ (uliftYonedaIsoYoneda.symm.app _) ≪≫ htO.homNatIso X
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) hk
  exact ⟨_, ⟨((preservesLimitIso uliftFunctor.{max u v, v} _).inv t').down⟩⟩
-/
theorem isFiltered [IsFiltered I] (hF : forall i, IsIndObject (F.obj i)) :
    IsFiltered (CostructuredArrow yoneda (colimit F)) := by
  -- It suffices to show that for any functor `G : J ⥤ CostructuredArrow yoneda (colimit F)` with
  -- `J` finite there is some `X` such that the set
  -- `lim Hom_{CostructuredArrow yoneda (colimit F)}(G·, X)` is nonempty.
  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  -- We begin by remarking that `lim Hom_{Over (colimit F)}(yG·, 𝟙 (colimit F))` is nonempty,
  -- simply because `𝟙 (colimit F)` is the terminal object. Here `y` is the functor
  -- `CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` induced by `yoneda`.
  have h₁ : Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver _ _).op ⋙
      yoneda.obj (Over.mk (𝟙 (colimit F))))) :=
    ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) (by simp)⟩
  -- `𝟙 (colimit F)` is the colimit of the diagram in `Over (colimit F)` given by the arrows of
  -- the form `Fi ⟶ colimit F`. Thus, pulling the colimit out of the hom functor and commuting
  -- the finite limit with the filtered colimit, we obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, 𝟙 (colimit F)) ≅`
  -- `colim_i lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i)`, and so we find `i` such that
  -- the limit is non-empty.
  obtain ⟨i, hi⟩ := exists_nonempty_limit_obj_of_isColimit F G _
    (colimit.isColimitToOver F) _ (Iso.refl _) h₁
  -- `F.obj i` is a small filtered colimit of representables, say of the functor `H : K ⥤ C`, so
  -- `𝟙 (F.obj i)` is the colimit of the arrows of the form `yHk ⟶ Fi` in `Over Fi`.
  -- Then `colimit.ι F i` is the colimit of the arrows of the form
  -- `H.obj F ⟶ F.obj i ⟶ colimit F` in `Over (colimit F)`.
  obtain ⟨⟨P⟩⟩ := hF i
  let hc : IsColimit ((Over.map (colimit.ι F i)).mapCocone P.cocone.toOver) :=
    isColimitOfPreserves (Over.map _) (Over.isColimitToOver P.coconeIsColimit)
  -- Again, we pull the colimit out of the hom functor and commute limit and colimit to obtain
  -- `lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i) ≅`
  -- `colim_k lim_j Hom_{Over (colimit F)}(yGj, yHk)`, and so we find `k` such that the limit
  -- is non-empty.
  obtain ⟨k, hk⟩ : exists k, Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
      yoneda.obj ((CostructuredArrow.toOver yoneda (colimit F)).obj <|
(CostructuredArrow.pre P.F yoneda (colimit F)).obj
(map (colimit.ι F i)).obj mk _))) :=
    exists_nonempty_limit_obj_of_isColimit F G _ hc _ (Iso.refl _) hi
  have htO : (CostructuredArrow.toOver yoneda (colimit F)).FullyFaithful := .ofFullyFaithful _
  -- Since the inclusion `y : CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` is fully
  -- faithful, `lim_j Hom_{Over (colimit F)}(yGj, yHk) ≅`
  -- `lim_j Hom_{CostructuredArrow yoneda (colimit F)}(Gj, Hk)` and so `Hk` is the object we're
  -- looking for.
  let q := fun X => isoWhiskerLeft _ (uliftYonedaIsoYoneda.symm.app _) ≪≫ htO.homNatIso X
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) hk
  exact ⟨_, ⟨((preservesLimitIso uliftFunctor.{max u v, v} _).inv t').down⟩⟩

end IndizationClosedUnderFilteredColimitsAux

/--
theorem `isIndObject_colimit` / 定理 `isIndObject_colimit`

English:
theorem isIndObject_colimit
  statement: (I : Type v) [SmallCategory I] [IsFiltered I]
  proof: by
  have : IsFiltered (CostructuredArrow yoneda (colimit F)) :=
    IndizationClosedUnderFilteredColimitsAux.isFiltered F hF
  refine (isIndObject_iff _).mpr ⟨this, ?_⟩
  -- It remains to show that `CostructuredArrow yoneda (colimit F)` is finally small. Because we
  -- have already shown it is filtered, it suffices to exhibit a small weakly terminal set. For this
  -- we use that all the `CostructuredArrow yoneda (F.obj i)` have small weakly terminal sets.
  have : forall i, exists (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
      forall i, exists j in s, Nonempty (i ⟶ j) :=
    fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
  choose s hs j hjs hj using this
  refine finallySmall_of_small_weakly_terminal_set
    (⋃ i, (map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
  obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
  let y' : CostructuredArrow yoneda (F.obj i) := mk (yonedaEquiv.symm y)
  obtain ⟨x⟩ := hj _ y'
  refine ⟨(map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
  · simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨i, j i y', hjs _ _, rfl⟩
  · refine ?_ ≫ (map (colimit.ι F i)).map x
    refine homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
    simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp, y']

中文:
定理 isIndObject_colimit
  结论: (I : 类型v) [小范畴 I] [是Filtered I]
  证明: by
  have : IsFiltered (CostructuredArrow yoneda (colimit F)) :=
    IndizationClosedUnderFilteredColimitsAux.isFiltered F hF
  refine (isIndObject_iff _).mpr ⟨this, ?_⟩
  -- It remains to show that `CostructuredArrow yoneda (colimit F)` is finally small. Because we
  -- have already shown it is filtered, it suffices to exhibit a small weakly terminal set. For this
  -- we use that all the `CostructuredArrow yoneda (F.obj i)` have small weakly terminal sets.
  have : forall i, exists (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
      forall i, exists j in s, Nonempty (i ⟶ j) :=
    fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
  choose s hs j hjs hj using this
  refine finallySmall_of_small_weakly_terminal_set
    (⋃ i, (map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
  obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
  let y' : CostructuredArrow yoneda (F.obj i) := mk (yonedaEquiv.symm y)
  obtain ⟨x⟩ := hj _ y'
  refine ⟨(map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
  · simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨i, j i y', hjs _ _, rfl⟩
  · refine ?_ ≫ (map (colimit.ι F i)).map x
    refine homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
    simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp, y']

Depends on / 依赖: CostructuredArrow, IndizationClosedUnderFilteredColimitsAux, IndizationClosedUnderFilteredColimitsAux.isFiltered, IsFiltered, colimit, isFiltered, isIndObject_iff, yoneda
-/
theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : forall i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  have : IsFiltered (CostructuredArrow yoneda (colimit F)) :=
    IndizationClosedUnderFilteredColimitsAux.isFiltered F hF
  refine (isIndObject_iff _).mpr ⟨this, ?_⟩
  -- It remains to show that `CostructuredArrow yoneda (colimit F)` is finally small. Because we
  -- have already shown it is filtered, it suffices to exhibit a small weakly terminal set. For this
  -- we use that all the `CostructuredArrow yoneda (F.obj i)` have small weakly terminal sets.
  have : forall i, exists (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
      forall i, exists j in s, Nonempty (i ⟶ j) :=
    fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
  choose s hs j hjs hj using this
  refine finallySmall_of_small_weakly_terminal_set
    (⋃ i, (map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
  obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
  let y' : CostructuredArrow yoneda (F.obj i) := mk (yonedaEquiv.symm y)
  obtain ⟨x⟩ := hj _ y'
  refine ⟨(map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
  · simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨i, j i y', hjs _ _, rfl⟩
  · refine ?_ ≫ (map (colimit.ι F i)).map x
    refine homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
    simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp, y']

end CategoryTheory.Limits
