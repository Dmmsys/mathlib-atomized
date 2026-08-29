/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Analysis.Normed.Group.SemiNormedGrp
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in SemiNormedGrp₁ and SemiNormedGrp

We show that `SemiNormedGrp₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGrp` has cokernels. We also show that
`SemiNormedGrp` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGrp` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGrp` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGrp₁

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `cokernelCocone` / `cokernelCocone` 的定义

English:
definition cokernelCocone
  signature: {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y)
  body: Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp]; rw [comp_apply]; rw [SemiNormedGrp₁.mkHom_apply]; rw [SemiNormedGrp₁.zero_apply]; rw [← Normed

中文:
定义 cokernelCocone
  签名: {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y)
  定义体: Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp]; rw [comp_apply]; rw [SemiNormedGrp₁.mkHom_apply]; rw [SemiNormedGrp₁.zero_apply]; rw [← Normed

Depends on / 依赖: Cofork, Cofork.of, Limits, Limits.zero_comp, NormedAddGroupHom, NormedAddGroupHom.isQuotientQuotient, NormedAddGroupHom.mem_ker, NormedAddGroupHom.range, comp_apply, f.hom, isQuotientQuotient, ker_normedMk, mem_ker, mem_range, mkHom_apply, norm_le, normedMk, range.ker_normedMk, range.normedMk, zero_apply
-/
def cokernelCocone {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp]; rw [comp_apply]; rw [SemiNormedGrp₁.mkHom_apply]; rw [SemiNormedGrp₁.zero_apply]; rw [← NormedAddGroupHom.mem_ker]; rw [f.hom.1.range.ker_normedMk]; rw [f.hom.1.mem_range]
      use x)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `cokernelLift` / `cokernelLift` 的定义

English:
definition cokernelLift
  signature: {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f)
  body: by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

中文:
定义 cokernelLift
  签名: {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f)
  定义体: by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

Depends on / 依赖: fconstructor
-/
def cokernelLift {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt := by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernels SemiNormedGrp₁.{u}
  body: HasColimit.mk
      { cocone := cokernelCocone f
        isColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)


中文:
实例 :
  签名: HasCokernels SemiNormedGrp₁.{u}
  定义体: HasColimit.mk
      { cocone := cokernelCocone f
        isColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)


Depends on / 依赖: HasColimit, HasColimit.mk, Hom.hom, NormedAddGroupHom, NormedAddGroupHom.lift_mk, NormedAddGroupHom.lift_unique, Subtype, Subtype.ext, Subtype.val, cocone, cokernelCocone, cokernelLift, congr_arg, hom_ext, isColimit, isColimitAux, lift_mk, lift_unique
-/
instance : HasCokernels SemiNormedGrp₁.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)
            fun _ _ w =>
SemiNormedGrp₁.hom_ext Subtype.ext
              (NormedAddGroupHom.lift_unique f.1.range _ _ _
                (congr_arg Subtype.val (congr_arg Hom.hom w))) }

-- Sanity check
example : HasCokernels SemiNormedGrp₁ := by infer_instance

end

end SemiNormedGrp₁

namespace SemiNormedGrp

section EqualizersAndKernels

noncomputable instance {V W : SemiNormedGrp.{u}} : Norm (V ⟶ W) where
  norm f := norm f.hom
noncomputable instance {V W : SemiNormedGrp.{u}} : NNNorm (V ⟶ W) where
  nnnorm f := nnnorm f.hom

/--
Definition of `fork` / `fork` 的定义

English:
definition fork
  signature: {V W : SemiNormedGrp.{u}} (f g : V ⟶ W)
  body: @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
(ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) by
    ext v
    have : v.1 in (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

中文:
定义 fork
  签名: {V W : SemiNormedGrp.{u}} (f g : V ⟶ W)
  定义体: @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
(ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) by
    ext v
    have : v.1 in (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

Depends on / 依赖: Fork.of, NormedAddGroupHom, NormedAddGroupHom.incl, NormedAddGroupHom.mem_ker, SetLike, SetLike.coe_mem, coe_mem, hom.ker, mem_ker, sub_eq_zero
-/
noncomputable def fork {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
(ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) by
    ext v
    have : v.1 in (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

/--
Instance `hasLimit_parallelPair` / 实例 `hasLimit_parallelPair`

English:
instance hasLimit_parallelPair
  signature: {V W : SemiNormedGrp.{u}} (f g : V ⟶ W)
  body: Nonempty.intro
      { cone := fork f g
        isLimit :=
          have := fun (c : Fork f g) =>
            show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
              rw [hom_sub]; rw [map_sub]; rw [AddMonoidHom.sub_apply]; rw [sub_eq_zero]
              exact congr_arg Hom.hom c.con

中文:
实例 hasLimit_parallelPair
  签名: {V W : SemiNormedGrp.{u}} (f g : V ⟶ W)
  定义体: Nonempty.intro
      { cone := fork f g
        isLimit :=
          have := fun (c : Fork f g) =>
            show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
              rw [hom_sub]; rw [map_sub]; rw [AddMonoidHom.sub_apply]; rw [sub_eq_zero]
              exact congr_arg Hom.hom c.con

Depends on / 依赖: AddMonoidHom, AddMonoidHom.sub_apply, Fork.IsLimit.mk, Hom.hom, IsLimit, Nonempty, Nonempty.intro, NormedAddGroupHom, NormedAddGroupHom.compHom, NormedAddGroupHom.ker.incl_comp_lift, NormedAddGroupHom.ker.lift, SemiNormedGrp, SemiNormedGrp.hom_ext, c.condition, compHom, condition, congr_arg, hom_ext, hom_sub, incl_comp_lift
-/
instance hasLimit_parallelPair {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) :
    HasLimit (parallelPair f g) where
  exists_limit :=
    Nonempty.intro
      { cone := fork f g
        isLimit :=
          have := fun (c : Fork f g) =>
            show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
              rw [hom_sub]; rw [map_sub]; rw [AddMonoidHom.sub_apply]; rw [sub_eq_zero]
              exact congr_arg Hom.hom c.condition
          Fork.IsLimit.mk _
            (fun c => ofHom <|
NormedAddGroupHom.ker.lift (Fork.ι c).hom _ this c)
            (fun _ => SemiNormedGrp.hom_ext <| NormedAddGroupHom.ker.incl_comp_lift _ _ (this _))
            fun c g h => by ext x; dsimp; simp_rw [← h]; rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasEqualizers.{u, u + 1} SemiNormedGrp
  body: @hasEqualizers_of_hasLimit_parallelPair SemiNormedGrp _ fun {_ _ f g} =>
    SemiNormedGrp.hasLimit_parallelPair f g

中文:
实例 :
  签名: Limits.HasEqualizers.{u, u + 1} SemiNormedGrp
  定义体: @hasEqualizers_of_hasLimit_parallelPair SemiNormedGrp _ fun {_ _ f g} =>
    SemiNormedGrp.hasLimit_parallelPair f g

Depends on / 依赖: SemiNormedGrp, SemiNormedGrp.hasLimit_parallelPair, hasEqualizers_of_hasLimit_parallelPair, hasLimit_parallelPair
-/
instance : Limits.HasEqualizers.{u, u + 1} SemiNormedGrp :=
  @hasEqualizers_of_hasLimit_parallelPair SemiNormedGrp _ fun {_ _ f g} =>
    SemiNormedGrp.hasLimit_parallelPair f g

end EqualizersAndKernels

section Cokernel

-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGrp₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.
/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
/--
Definition of `cokernelCocone` / `cokernelCocone` 的定义

English:
definition cokernelCocone
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  body: Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

中文:
定义 cokernelCocone
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  定义体: Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

Depends on / 依赖: Cofork, Cofork.of, NormedAddGroupHom, NormedAddGroupHom.range, SemiNormedGrp, SemiNormedGrp.of, f.hom, f.hom.range.normedMk, normedMk
-/
def cokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
/--
Definition of `cokernelLift` / `cokernelLift` 的定义

English:
definition cokernelLift
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f)
  body: ofHom NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

中文:
定义 cokernelLift
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f)
  定义体: ofHom NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.lift
-/
def cokernelLift {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt :=
ofHom NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
/--
Definition of `isColimitCokernelCocone` / `isColimitCokernelCocone` 的定义

English:
definition isColimitCokernelCocone
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  body: isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
fun _ _ w => SemiNormedGrp.hom_ext NormedAddGroupHom.lift_unique f.hom.range _ _ _
      congr_arg Hom.hom w

中文:
定义 isColimitCokernelCocone
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  定义体: isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
fun _ _ w => SemiNormedGrp.hom_ext NormedAddGroupHom.lift_unique f.hom.range _ _ _
      congr_arg Hom.hom w

Depends on / 依赖: Hom.hom, NormedAddGroupHom, NormedAddGroupHom.lift_mk, NormedAddGroupHom.lift_unique, SemiNormedGrp, SemiNormedGrp.hom_ext, cokernelLift, congr_arg, f.hom.range, hom_ext, isColimitAux, lift_mk, lift_unique
-/
def isColimitCokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    IsColimit (cokernelCocone f) :=
  isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
fun _ _ w => SemiNormedGrp.hom_ext NormedAddGroupHom.lift_unique f.hom.range _ _ _
      congr_arg Hom.hom w

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernels SemiNormedGrp.{u}
  body: HasColimit.mk
      { cocone := cokernelCocone f
        isColimit := isColimitCokernelCocone f }

中文:
实例 :
  签名: HasCokernels SemiNormedGrp.{u}
  定义体: HasColimit.mk
      { cocone := cokernelCocone f
        isColimit := isColimitCokernelCocone f }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, cokernelCocone, isColimit, isColimitCokernelCocone
-/
instance : HasCokernels SemiNormedGrp.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit := isColimitCokernelCocone f }

-- Sanity check
example : HasCokernels SemiNormedGrp := by infer_instance

section ExplicitCokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
noncomputable
/--
Definition of `explicitCokernel` / `explicitCokernel` 的定义

English:
definition explicitCokernel
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  body: (cokernelCocone f).pt

中文:
定义 explicitCokernel
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  定义体: (cokernelCocone f).pt

Depends on / 依赖: cokernelCocone
-/
def explicitCokernel {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : SemiNormedGrp.{u} :=
  (cokernelCocone f).pt

/-- Descend to the explicit cokernel. -/
noncomputable
/--
Definition of `explicitCokernelDesc` / `explicitCokernelDesc` 的定义

English:
definition explicitCokernelDesc
  signature: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0)
  body: (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

中文:
定义 explicitCokernelDesc
  签名: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0)
  定义体: (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

Depends on / 依赖: Cofork, Cofork.of, isColimitCokernelCocone
-/
def explicitCokernelDesc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicitCokernel f ⟶ Z :=
  (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
noncomputable
/--
Definition of `explicitCokernelπ` / `explicitCokernelπ` 的定义

English:
definition explicitCokernelπ
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  body: (cokernelCocone f).ι.app WalkingParallelPair.one

中文:
定义 explicitCokernelπ
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  定义体: (cokernelCocone f).ι.app WalkingParallelPair.one

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one, cokernelCocone
-/
def explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Y ⟶ explicitCokernel f :=
  (cokernelCocone f).ι.app WalkingParallelPair.one

/--
theorem `explicitCokernelπ_surjective` / 定理 `explicitCokernelπ_surjective`

English:
theorem explicitCokernelπ_surjective
  given: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y}
  proof: Quot.mk_surjective

中文:
定理 explicitCokernelπ_surjective
  条件: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y}
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem explicitCokernelπ_surjective {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicitCokernelπ f) :=
  Quot.mk_surjective

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `comp_explicitCokernelπ` / 定理 `comp_explicitCokernelπ`

English:
theorem comp_explicitCokernelπ
  given: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  proof: by
  convert! (cokernelCocone f).w WalkingParallelPairHom.left
  simp

@[simp]

中文:
定理 comp_explicitCokernelπ
  条件: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  证明: by
  convert! (cokernelCocone f).w WalkingParallelPairHom.left
  simp

@[simp]

Depends on / 依赖: WalkingParallelPairHom, WalkingParallelPairHom.left, cokernelCocone, convert
-/
theorem comp_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    f ≫ explicitCokernelπ f = 0 := by
  convert! (cokernelCocone f).w WalkingParallelPairHom.left
  simp

@[simp]
/--
theorem `explicitCokernelπ_apply_dom_eq_zero` / 定理 `explicitCokernelπ_apply_dom_eq_zero`

English:
theorem explicitCokernelπ_apply_dom_eq_zero
  given: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} (x : X)
  proof: show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicitCokernelπ]; rfl

@[simp, reassoc]

中文:
定理 explicitCokernelπ_apply_dom_eq_zero
  条件: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} (x : X)
  证明: show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicitCokernelπ]; rfl

@[simp, reassoc]
-/
theorem explicitCokernelπ_apply_dom_eq_zero {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} (x : X) :
    (explicitCokernelπ f) (f x) = 0 :=
  show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicitCokernelπ]; rfl

@[simp, reassoc]
/--
theorem `explicitCokernelπ_desc` / 定理 `explicitCokernelπ_desc`

English:
theorem explicitCokernelπ_desc
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: (isColimitCokernelCocone f).fac _ _

@[simp]

中文:
定理 explicitCokernelπ_desc
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: (isColimitCokernelCocone f).fac _ _

@[simp]

Depends on / 依赖: isColimitCokernelCocone
-/
theorem explicitCokernelπ_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : explicitCokernelπ f ≫ explicitCokernelDesc w = g :=
  (isColimitCokernelCocone f).fac _ _

@[simp]
/--
theorem `explicitCokernelπ_desc_apply` / 定理 `explicitCokernelπ_desc_apply`

English:
theorem explicitCokernelπ_desc_apply
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicitCokernelπ_desc]

中文:
定理 explicitCokernelπ_desc_apply
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicitCokernelπ_desc]

Depends on / 依赖: explicitCokernelDesc
-/
theorem explicitCokernelπ_desc_apply {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (x : Y) : explicitCokernelDesc cond (explicitCokernelπ f x) = g x :=
  show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicitCokernelπ_desc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `explicitCokernelDesc_unique` / 定理 `explicitCokernelDesc_unique`

English:
theorem explicitCokernelDesc_unique
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: by
  apply (isColimitCokernelCocone f).uniq (Cofork.ofπ g (by simp [w]))
  rintro (_ | _)
  · convert! w.symm
    simp
  · exact he

中文:
定理 explicitCokernelDesc_unique
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: by
  apply (isColimitCokernelCocone f).uniq (Cofork.ofπ g (by simp [w]))
  rintro (_ | _)
  · convert! w.symm
    simp
  · exact he

Depends on / 依赖: Cofork, Cofork.of, convert, isColimitCokernelCocone, w.symm
-/
theorem explicitCokernelDesc_unique {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) (e : explicitCokernel f ⟶ Z) (he : explicitCokernelπ f ≫ e = g) :
    e = explicitCokernelDesc w := by
  apply (isColimitCokernelCocone f).uniq (Cofork.ofπ g (by simp [w]))
  rintro (_ | _)
  · convert! w.symm
    simp
  · exact he

/--
theorem `explicitCokernelDesc_comp_eq_desc` / 定理 `explicitCokernelDesc_comp_eq_desc`

English:
theorem explicitCokernelDesc_comp_eq_desc
  statement: {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: by
  refine explicitCokernelDesc_unique _ _ ?_
  rw [← CategoryTheory.Category.assoc]; rw [explicitCokernelπ_desc]

@[simp]

中文:
定理 explicitCokernelDesc_comp_eq_desc
  结论: {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: by
  refine explicitCokernelDesc_unique _ _ ?_
  rw [← CategoryTheory.Category.assoc]; rw [explicitCokernelπ_desc]

@[simp]

Depends on / 依赖: Category, CategoryTheory, CategoryTheory.Category.assoc, explicitCokernelDesc_unique
-/
theorem explicitCokernelDesc_comp_eq_desc {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} {cond : f ≫ g = 0} :
    explicitCokernelDesc cond ≫ h =
      explicitCokernelDesc
        (show f ≫ g ≫ h = 0 by rw [← CategoryTheory.Category.assoc, cond, Limits.zero_comp]) := by
  refine explicitCokernelDesc_unique _ _ ?_
  rw [← CategoryTheory.Category.assoc]; rw [explicitCokernelπ_desc]

@[simp]
/--
theorem `explicitCokernelDesc_zero` / 定理 `explicitCokernelDesc_zero`

English:
theorem explicitCokernelDesc_zero
  given: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  proof: Eq.symm explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero

@[ext]

中文:
定理 explicitCokernelDesc_zero
  条件: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  证明: Eq.symm explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero

@[ext]

Depends on / 依赖: CategoryTheory, CategoryTheory.Limits.comp_zero, Eq.symm, Limits, comp_zero, explicitCokernelDesc_unique
-/
theorem explicitCokernelDesc_zero {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    explicitCokernelDesc (show f ≫ (0 : Y ⟶ Z) = 0 from CategoryTheory.Limits.comp_zero) = 0 :=
Eq.symm explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero

@[ext]
/--
theorem `explicitCokernel_hom_ext` / 定理 `explicitCokernel_hom_ext`

English:
theorem explicitCokernel_hom_ext
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  proof: by
  let g : Y ⟶ Z := explicitCokernelπ f ≫ e₂
  have w : f ≫ g = 0 := by simp [g]
  have : e₂ = explicitCokernelDesc w := by apply explicitCokernelDesc_unique; rfl
  rw [this]
  apply explicitCokernelDesc_unique
  exact h

中文:
定理 explicitCokernel_hom_ext
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  证明: by
  let g : Y ⟶ Z := explicitCokernelπ f ≫ e₂
  have w : f ≫ g = 0 := by simp [g]
  have : e₂ = explicitCokernelDesc w := by apply explicitCokernelDesc_unique; rfl
  rw [this]
  apply explicitCokernelDesc_unique
  exact h

Depends on / 依赖: explicitCokernelDesc, explicitCokernelDesc_unique
-/
theorem explicitCokernel_hom_ext {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    (e₁ e₂ : explicitCokernel f ⟶ Z) (h : explicitCokernelπ f ≫ e₁ = explicitCokernelπ f ≫ e₂) :
    e₁ = e₂ := by
  let g : Y ⟶ Z := explicitCokernelπ f ≫ e₂
  have w : f ≫ g = 0 := by simp [g]
  have : e₂ = explicitCokernelDesc w := by apply explicitCokernelDesc_unique; rfl
  rw [this]
  apply explicitCokernelDesc_unique
  exact h

/--
Instance `explicitCokernelπ.epi` / 实例 `explicitCokernelπ.epi`

English:
instance explicitCokernelπ.epi
  signature: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y}
  body: by
  constructor
  intro Z g h H
  ext x
  rw [H]

中文:
实例 explicitCokernelπ.epi
  签名: {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y}
  定义体: by
  constructor
  intro Z g h H
  ext x
  rw [H]
-/
instance explicitCokernelπ.epi {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Epi (explicitCokernelπ f) := by
  constructor
  intro Z g h H
  ext x
  rw [H]

/--
theorem `isQuotient_explicitCokernelπ` / 定理 `isQuotient_explicitCokernelπ`

English:
theorem isQuotient_explicitCokernelπ
  given: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  proof: NormedAddGroupHom.isQuotientQuotient _

中文:
定理 isQuotient_explicitCokernelπ
  条件: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  证明: NormedAddGroupHom.isQuotientQuotient _

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.isQuotientQuotient, isQuotientQuotient
-/
theorem isQuotient_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    NormedAddGroupHom.IsQuotient (explicitCokernelπ f).hom :=
  NormedAddGroupHom.isQuotientQuotient _

/--
theorem `normNoninc_explicitCokernelπ` / 定理 `normNoninc_explicitCokernelπ`

English:
theorem normNoninc_explicitCokernelπ
  given: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  proof: (isQuotient_explicitCokernelπ f).norm_le

中文:
定理 normNoninc_explicitCokernelπ
  条件: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  证明: (isQuotient_explicitCokernelπ f).norm_le

Depends on / 依赖: norm_le
-/
theorem normNoninc_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    (explicitCokernelπ f).hom.NormNoninc :=
  (isQuotient_explicitCokernelπ f).norm_le

open scoped NNReal

/--
theorem `explicitCokernelDesc_norm_le_of_norm_le` / 定理 `explicitCokernelDesc_norm_le_of_norm_le`

English:
theorem explicitCokernelDesc_norm_le_of_norm_le
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  proof: NormedAddGroupHom.lift_norm_le _ _ _ h

中文:
定理 explicitCokernelDesc_norm_le_of_norm_le
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
  证明: NormedAddGroupHom.lift_norm_le _ _ _ h

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.lift_norm_le, lift_norm_le
-/
theorem explicitCokernelDesc_norm_le_of_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} (w : f ≫ g = 0) (c : Real>=0) (h : ‖g‖ <= c) : ‖explicitCokernelDesc w‖ <= c :=
  NormedAddGroupHom.lift_norm_le _ _ _ h

/--
theorem `explicitCokernelDesc_normNoninc` / 定理 `explicitCokernelDesc_normNoninc`

English:
theorem explicitCokernelDesc_normNoninc
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: by
  refine NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 ?_
  rw [← NNReal.coe_one]
  exact
    explicitCokernelDesc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)

中文:
定理 explicitCokernelDesc_normNoninc
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: by
  refine NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 ?_
  rw [← NNReal.coe_one]
  exact
    explicitCokernelDesc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)

Depends on / 依赖: NNReal, NNReal.coe_one, NormNoninc, NormedAddGroupHom, NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one, coe_one, explicitCokernelDesc_norm_le_of_norm_le, normNoninc_iff_norm_le_one
-/
theorem explicitCokernelDesc_normNoninc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (hg : g.hom.NormNoninc) : (explicitCokernelDesc cond).hom.NormNoninc := by
  refine NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 ?_
  rw [← NNReal.coe_one]
  exact
    explicitCokernelDesc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)

/--
theorem `explicitCokernelDesc_comp_eq_zero` / 定理 `explicitCokernelDesc_comp_eq_zero`

English:
theorem explicitCokernelDesc_comp_eq_zero
  statement: {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: by
  rw [← cancel_epi (explicitCokernelπ f)]; rw [← Category.assoc]; rw [explicitCokernelπ_desc]
  simp [cond2]

中文:
定理 explicitCokernelDesc_comp_eq_zero
  结论: {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: by
  rw [← cancel_epi (explicitCokernelπ f)]; rw [← Category.assoc]; rw [explicitCokernelπ_desc]
  simp [cond2]

Depends on / 依赖: Category, Category.assoc, cancel_epi
-/
theorem explicitCokernelDesc_comp_eq_zero {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) : explicitCokernelDesc cond ≫ h = 0 := by
  rw [← cancel_epi (explicitCokernelπ f)]; rw [← Category.assoc]; rw [explicitCokernelπ_desc]
  simp [cond2]

/--
theorem `explicitCokernelDesc_norm_le` / 定理 `explicitCokernelDesc_norm_le`

English:
theorem explicitCokernelDesc_norm_le
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl

中文:
定理 explicitCokernelDesc_norm_le
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl

Depends on / 依赖: explicitCokernelDesc_norm_le_of_norm_le, le_rfl
-/
theorem explicitCokernelDesc_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : ‖explicitCokernelDesc w‖ <= ‖g‖ :=
  explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
noncomputable
/--
Definition of `explicitCokernelIso` / `explicitCokernelIso` 的定义

English:
definition explicitCokernelIso
  signature: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  body: (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)

中文:
定义 explicitCokernelIso
  签名: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  定义体: (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)

Depends on / 依赖: coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitCokernelCocone
-/
def explicitCokernelIso {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernel f ≅ cokernel f :=
  (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `explicitCokernelIso_hom_π` / 定理 `explicitCokernelIso_hom_π`

English:
theorem explicitCokernelIso_hom_π
  given: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  proof: by
  simp [explicitCokernelπ, explicitCokernelIso, IsColimit.coconePointUniqueUpToIso]

中文:
定理 explicitCokernelIso_hom_π
  条件: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  证明: by
  simp [explicitCokernelπ, explicitCokernelIso, IsColimit.coconePointUniqueUpToIso]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, explicitCokernelIso
-/
theorem explicitCokernelIso_hom_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernelπ f ≫ (explicitCokernelIso f).hom = cokernel.π _ := by
  simp [explicitCokernelπ, explicitCokernelIso, IsColimit.coconePointUniqueUpToIso]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `explicitCokernelIso_inv_π` / 定理 `explicitCokernelIso_inv_π`

English:
theorem explicitCokernelIso_inv_π
  given: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  proof: by
  simp [explicitCokernelπ, explicitCokernelIso]

中文:
定理 explicitCokernelIso_inv_π
  条件: {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y)
  证明: by
  simp [explicitCokernelπ, explicitCokernelIso]

Depends on / 依赖: explicitCokernelIso
-/
theorem explicitCokernelIso_inv_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    cokernel.π f ≫ (explicitCokernelIso f).inv = explicitCokernelπ f := by
  simp [explicitCokernelπ, explicitCokernelIso]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `explicitCokernelIso_hom_desc` / 定理 `explicitCokernelIso_hom_desc`

English:
theorem explicitCokernelIso_hom_desc
  statement: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: by
  ext1
  simp [explicitCokernelDesc, explicitCokernelπ, explicitCokernelIso,
    IsColimit.coconePointUniqueUpToIso]

中文:
定理 explicitCokernelIso_hom_desc
  结论: {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: by
  ext1
  simp [explicitCokernelDesc, explicitCokernelπ, explicitCokernelIso,
    IsColimit.coconePointUniqueUpToIso]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, explicitCokernelDesc, explicitCokernelIso
-/
theorem explicitCokernelIso_hom_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) :
    (explicitCokernelIso f).hom ≫ cokernel.desc f g w = explicitCokernelDesc w := by
  ext1
  simp [explicitCokernelDesc, explicitCokernelπ, explicitCokernelIso,
    IsColimit.coconePointUniqueUpToIso]

/--
Definition of `explicitCokernel.map` / `explicitCokernel.map` 的定义

English:
definition explicitCokernel.map
  signature: {A B C D : SemiNormedGrp.{u}}
  body: @explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) by simp [reassoc_of% h]

中文:
定义 explicitCokernel.map
  签名: {A B C D : SemiNormedGrp.{u}}
  定义体: @explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) by simp [reassoc_of% h]

Depends on / 依赖: explicitCokernelDesc, reassoc_of
-/
noncomputable def explicitCokernel.map {A B C D : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) :
    explicitCokernel fab ⟶ explicitCokernel fcd :=
@explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) by simp [reassoc_of% h]

/--
theorem `ExplicitCoker.map_desc` / 定理 `ExplicitCoker.map_desc`

English:
theorem ExplicitCoker.map_desc
  statement: {A B C D B' D' : SemiNormedGrp.{u}}
  proof: by
  delta explicitCokernel.map
  simp only [← Category.assoc, ← cancel_epi (explicitCokernelπ fab)]
  simp [Category.assoc, explicitCokernelπ_desc, h']

中文:
定理 ExplicitCoker.map_desc
  结论: {A B C D B' D' : SemiNormedGrp.{u}}
  证明: by
  delta explicitCokernel.map
  simp only [← Category.assoc, ← cancel_epi (explicitCokernelπ fab)]
  simp [Category.assoc, explicitCokernelπ_desc, h']

Depends on / 依赖: Category, Category.assoc, cancel_epi, explicitCokernel, explicitCokernel.map
-/
theorem ExplicitCoker.map_desc {A B C D B' D' : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} {h : fab ≫ fbd = fac ≫ fcd}
    {fbb' : B ⟶ B'} {fdd' : D ⟶ D'} {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
    (h' : fbb' ≫ g = fbd ≫ fdd') :
    explicitCokernelDesc condb ≫ g = explicitCokernel.map h ≫ explicitCokernelDesc condd := by
  delta explicitCokernel.map
  simp only [← Category.assoc, ← cancel_epi (explicitCokernelπ fab)]
  simp [Category.assoc, explicitCokernelπ_desc, h']

end ExplicitCokernel

end Cokernel

end SemiNormedGrp
