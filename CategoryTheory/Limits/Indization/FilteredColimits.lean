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

/-- (implementation) Pulling out a colimit out of a hom functor is one half of the key lemma. Note
that all of the heavy lifting actually happens in `CostructuredArrow.toOverCompYonedaColimit`
and `yonedaYonedaColimit`. -/
/-
**CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.compYonedaColim
itIsoColimitCompYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Indizati
onClosedUnderFilteredColimitsAux`。
形式化陈述：compYonedaColimitIsoColimitCompYoneda : 𝒢 ⋙ yoneda.obj (colimit H) ≅ colim
it (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) Pulling out a colimit out of a hom functor is one half of the k
ey lemma. Note
that all of the heavy lifting actually happens in `CostructuredArrow.toOverCompY
onedaColimit`
and `yonedaYonedaColimit`.
-/
noncomputable def compYonedaColimitIsoColimitCompYoneda :
    𝒢 ⋙ yoneda.obj (colimit H) ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := calc
  𝒢 ⋙ yoneda.obj (colimit H) ≅ 𝒢 ⋙ colimit (H ⋙ yoneda) :=
        isoWhiskerLeft G.op (toOverCompYonedaColimit H)
  _ ≅ 𝒢 ⋙ (H ⋙ yoneda).flip ⋙ colim := isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip ⋙ colim := Iso.refl _
  _ ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := (colimitIsoFlipCompColim _).symm
/-
**CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.exists_nonempty
_limit_obj_of_colimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Indizatio
nClosedUnderFilteredColimitsAux`。
形式化陈述：exists_nonempty_limit_obj_of_colimit [IsFiltered K] (h : Nonempty (limit <
| 𝒢 ⋙ yoneda.obj (colimit H))) : exists k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.
obj k))
参数：h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj (colimit H))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
theorem exists_nonempty_limit_obj_of_colimit [IsFiltered K]
    (h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj (colimit H))) :
    ∃ k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.obj k)) := by
  obtain ⟨t⟩ := h
  let t₂ := limMap (compYonedaColimitIsoColimitCompYoneda F G H).hom t
  let t₃ := (colimitLimitIso (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip k).hom y
  let y := flipCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) k
  exact (lim.mapIso y).hom z
/-
**CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.exists_nonempty
_limit_obj_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Indizat
ionClosedUnderFilteredColimitsAux`。
形式化陈述：exists_nonempty_limit_obj_of_isColimit [IsFiltered K] {c : Cocone H} (hc :
 IsColimit c) (T : Over (colimit F)) (hT : c.pt ≅ T) (h : Nonempty (limit <| 𝒢 ⋙
 yoneda.obj T)) : exists k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.obj k))
参数：hc : IsColimit c；T : Over (colimit F)；hT : c.pt ≅ T；h : Nonempty (limit <| 𝒢 
⋙ yoneda.obj T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.exists_no
nempty_limit_obj_of_colimit`：exists_nonempty_limit_obj_of_colimit [IsFiltered K]
 (h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj (colimit H))) : exists k, Nonempty (limi
t <| 𝒢 ⋙ …
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
-/
theorem exists_nonempty_limit_obj_of_isColimit [IsFiltered K] {c : Cocone H} (hc : IsColimit c)
    (T : Over (colimit F)) (hT : c.pt ≅ T)
    (h : Nonempty (limit <| 𝒢 ⋙ yoneda.obj T)) :
    ∃ k, Nonempty (limit <| 𝒢 ⋙ yoneda.obj (H.obj k)) := by
  refine exists_nonempty_limit_obj_of_colimit F G H ?_
  suffices T ≅ colimit H from Nonempty.map (lim.map (whiskerLeft 𝒢 (yoneda.map this.hom))) h
  refine hT.symm ≪≫ IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

end Interchange

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.isFiltered** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.IndizationClosedUnderFilteredColimi
tsAux`。
形式化陈述：isFiltered [IsFiltered I] (hF : forall i, IsIndObject (F.obj i)) : IsFilte
red (CostructuredArrow yoneda (colimit F))
参数：hF : forall i, IsIndObject (F.obj i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsFiltered.iff_nonempty_limit`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C],   CategoryTheory.IsFiltered C ↔     ∀ {J : Type 
v} [inst_1 : CategoryTheory.SmallC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.exists_no
nempty_limit_obj_of_isColimit`：exists_nonempty_limit_obj_of_isColimit [IsFiltere
d K] {c : Cocone H} (hc : IsColimit c) (T : Over (colimit F)) (hT : c.pt ≅ T) (h
 : Nonempty…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instIsFilteredI`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (T
ype v)}   (P : CategoryTheory.Limits.IndObjectPre…
· 使用定理 `CategoryTheory.CostructuredArrow.instFullOverToOver`：∀ {T : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.CostructuredArrow.instFaithfulOverToOver`：∀ {T : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
theorem isFiltered [IsFiltered I] (hF : ∀ i, IsIndObject (F.obj i)) :
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
  --   `colim_i lim_j Hom_{Over (colimit F)}(yGj, colimit.ι F i)`, and so we find `i` such that
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
  --   `colim_k lim_j Hom_{Over (colimit F)}(yGj, yHk)`, and so we find `k` such that the limit
  -- is non-empty.
  obtain ⟨k, hk⟩ : ∃ k, Nonempty (limit (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
      yoneda.obj ((CostructuredArrow.toOver yoneda (colimit F)).obj <|
        (CostructuredArrow.pre P.F yoneda (colimit F)).obj <|
          (map (colimit.ι F i)).obj <| mk _))) :=
    exists_nonempty_limit_obj_of_isColimit F G _ hc _ (Iso.refl _) hi
  have htO : (CostructuredArrow.toOver yoneda (colimit F)).FullyFaithful := .ofFullyFaithful _
  -- Since the inclusion `y : CostructuredArrow yoneda (colimit F) ⥤ Over (colimit F)` is fully
  -- faithful, `lim_j Hom_{Over (colimit F)}(yGj, yHk) ≅`
  --   `lim_j Hom_{CostructuredArrow yoneda (colimit F)}(Gj, Hk)` and so `Hk` is the object we're
  -- looking for.
  let q := fun X => isoWhiskerLeft _ (uliftYonedaIsoYoneda.symm.app _) ≪≫ htO.homNatIso X
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) hk
  exact ⟨_, ⟨((preservesLimitIso uliftFunctor.{max u v, v} _).inv t').down⟩⟩

end IndizationClosedUnderFilteredColimitsAux

/-
**CategoryTheory.Limits.isIndObject_colimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isIndObject_colimit (I : Type v) [SmallCategory I] [IsFiltered I] (F : I ⥤
 Cᵒᵖ ⥤ Type v) (hF : forall i, IsIndObject (F.obj i)) : IsIndObject (colimit F)
参数：I : Type v；F : I ⥤ Cᵒᵖ ⥤ Type v；hF : forall i, IsIndObject (F.obj i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.IndizationClosedUnderFilteredColimitsAux.isFiltere
d`：isFiltered [IsFiltered I] (hF : forall i, IsIndObject (F.obj i)) : IsFiltered
 (CostructuredArrow yoneda (colimit F))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.isIndObject_iff`：isIndObject_iff (A : Cᵒᵖ ⥤ Type v
) : IsIndObject A ↔ (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} 
(CostructuredArrow yoneda A…
· 使用定理 `CategoryTheory.FinallySmall.exists_small_weakly_terminal_set`：∀ (J : Typ
e u) [inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.FinallySmall J], 
  ∃ s, ∃ (_ : Small.{w, u} ↑s), ∀ (i : J), ∃ j ∈ s…
· 使用定理 `CategoryTheory.Limits.IsIndObject.finallySmall`：finallySmall (h : IsIndO
bject A) : FinallySmall.{v} (CostructuredArrow yoneda A)
· 使用定理 `CategoryTheory.finallySmall_of_small_weakly_terminal_set`：finallySmall_o
f_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s] (hs 
: forall i, exists j in s, Nonempty (i ⟶ j)) :…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.FunctorToTypes.jointly_surjective'`：jointly_surjective' [
forall k, HasColimit (F.flip.obj k)] (k : K) (x : (colimit F).obj k) : exists j 
y, x = (colimit.ι F j).app k y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  have : IsFiltered (CostructuredArrow yoneda (colimit F)) :=
    IndizationClosedUnderFilteredColimitsAux.isFiltered F hF
  refine (isIndObject_iff _).mpr ⟨this, ?_⟩
  -- It remains to show that `CostructuredArrow yoneda (colimit F)` is finally small. Because we
  -- have already shown it is filtered, it suffices to exhibit a small weakly terminal set. For this
  -- we use that all the `CostructuredArrow yoneda (F.obj i)` have small weakly terminal sets.
  have : ∀ i, ∃ (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
      ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) :=
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

