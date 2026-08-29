/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ιZeroIsIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.liftMono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ιOfZero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing work in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable [HasZeroMorphisms C]

/--
Definition of `HasKernel` / `HasKernel` 的定义

English:
abbreviation HasKernel
  signature: {X Y : C} (f : X ⟶ Y)
  body: HasLimit (parallelPair f 0)

中文:
缩写 HasKernel
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: HasLimit (parallelPair f 0)

Depends on / 依赖: HasLimit, parallelPair
-/
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

/--
Definition of `HasCokernel` / `HasCokernel` 的定义

English:
abbreviation HasCokernel
  signature: {X Y : C} (f : X ⟶ Y)
  body: HasColimit (parallelPair f 0)

中文:
缩写 HasCokernel
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: HasColimit (parallelPair f 0)

Depends on / 依赖: HasColimit, parallelPair
-/
abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

section

/--
Definition of `KernelFork` / `KernelFork` 的定义

English:
abbreviation KernelFork
  body: Fork f 0

中文:
缩写 核叉
  定义体: Fork f 0
-/
abbrev KernelFork :=
  Fork f 0

variable {f}

@[reassoc (attr := simp)]
/--
theorem `KernelFork.condition` / 定理 `KernelFork.condition`

English:
theorem KernelFork.condition
  given: (s : KernelFork f)
  statement: Fork.ι s ≫ f = 0
  proof: by
  rw [Fork.condition]; rw [HasZeroMorphisms.comp_zero]

中文:
定理 核叉.condition
  条件: (s : 核叉 f)
  结论: 叉.ι s ≫ f = 0
  证明: by
  rw [Fork.condition]; rw [HasZeroMorphisms.comp_zero]

Depends on / 依赖: Fork.condition, HasZeroMorphisms, HasZeroMorphisms.comp_zero, comp_zero, condition
-/
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  rw [Fork.condition]; rw [HasZeroMorphisms.comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `KernelFork.app_one` / 定理 `KernelFork.app_one`

English:
theorem KernelFork.app_one
  given: (s : KernelFork f)
  statement: s.π.app one = 0
  proof: by
  simp

中文:
定理 核叉.app_one
  条件: (s : 核叉 f)
  结论: s.π.app one = 0
  证明: by
  simp
-/
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  simp

/--
Definition of `KernelFork.ofι` / `KernelFork.ofι` 的定义

English:
abbreviation KernelFork.ofι
  signature: {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0)
  body: Fork.ofι ι by rw [w, HasZeroMorphisms.comp_zero]

@[simp]

中文:
缩写 核叉.ofι
  签名: {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0)
  定义体: Fork.ofι ι by rw [w, HasZeroMorphisms.comp_zero]

@[simp]

Depends on / 依赖: Fork.of, HasZeroMorphisms, HasZeroMorphisms.comp_zero, comp_zero
-/
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
Fork.ofι ι by rw [w, HasZeroMorphisms.comp_zero]

@[simp]
/--
theorem `KernelFork.ι_ofι` / 定理 `KernelFork.ι_ofι`

English:
theorem KernelFork.ι_ofι
  given: {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0)
  proof: rfl

中文:
定理 核叉.ι_ofι
  条件: {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0)
  证明: rfl
-/
theorem KernelFork.ι_ofι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
    Fork.ι (KernelFork.ofι ι w) = ι := rfl

section

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoOfι` / `isoOfι` 的定义

English:
definition isoOfι
  signature: (s : Fork f 0)
  body: Cone.ext (Iso.refl _) by aesop

中文:
定义 isoOfι
  签名: (s : 叉 f 0)
  定义体: Cone.ext (Iso.refl _) by aesop

Depends on / 依赖: Cone.ext, Iso.refl
-/
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
Cone.ext (Iso.refl _) by aesop

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofιCongr` / `ofιCongr` 的定义

English:
definition ofιCongr
  signature: {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι')
  body: Cone.ext (Iso.refl _)

中文:
定义 ofιCongr
  签名: {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι')
  定义体: Cone.ext (Iso.refl _)

Depends on / 依赖: Cone.ext, Iso.refl
-/
def ofιCongr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    KernelFork.ofι ι w ≅ KernelFork.ofι ι' (by rw [← h, w]) :=
  Cone.ext (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `compNatIso` / `compNatIso` 的定义

English:
definition compNatIso
  signature: {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [F.IsEquivalence]
  body: let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | zero => Iso.refl _
    | one => Iso.refl _
NatIso.ofComponents app by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> aesop

中文:
定义 comp自然数Iso
  签名: {D : 类型u'} [范畴.{v} D] [有ZeroMorphisms D] (F : C ⥤ D) [F.是等价]
  定义体: let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | zero => Iso.refl _
    | one => Iso.refl _
NatIso.ofComponents app by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> aesop

Depends on / 依赖: F.map, Iso.refl, NatIso, NatIso.ofComponents, WalkingParallelPair, ofComponents, parallelPair
-/
def compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [F.IsEquivalence] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | zero => Iso.refl _
    | one => Iso.refl _
NatIso.ofComponents app by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> aesop

end

/--
Definition of `KernelFork.IsLimit.lift'` / `KernelFork.IsLimit.lift'` 的定义

English:
definition KernelFork.IsLimit.lift'
  signature: {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
  body: ⟨hs.lift KernelFork.ofι _ h, hs.fac _ _⟩

中文:
定义 核叉.是极限.lift'
  签名: {s : 核叉 f} (hs : 是极限 s) {W : C} (k : W ⟶ X)
  定义体: ⟨hs.lift KernelFork.ofι _ h, hs.fac _ _⟩

Depends on / 依赖: KernelFork, KernelFork.of, hs.fac, hs.lift
-/
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = 0) : { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
⟨hs.lift KernelFork.ofι _ h, hs.fac _ _⟩

/--
Definition of `isLimitAux` / `isLimitAux` 的定义

English:
definition isLimitAux
  signature: (t : KernelFork f) (lift : forall s : KernelFork f, s.pt ⟶ t.pt)
  body: { lift
    fac := fun s j => by
      cases j
      · exact fac s
      · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

中文:
定义 isLimitAux
  签名: (t : 核叉 f) (lift : 对任意 s : 核叉 f, s.pt ⟶ t.pt)
  定义体: { lift
    fac := fun s j => by
      cases j
      · exact fac s
      · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

Depends on / 依赖: Limits, Limits.WalkingParallelPair.zero, WalkingParallelPair
-/
def isLimitAux (t : KernelFork f) (lift : forall s : KernelFork f, s.pt ⟶ t.pt)
    (fac : forall s : KernelFork f, lift s ≫ t.ι = s.ι)
    (uniq : forall (s : KernelFork f) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => by
      cases j
      · exact fac s
      · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

/--
Definition of `KernelFork.IsLimit.ofι` / `KernelFork.IsLimit.ofι` 的定义

English:
definition KernelFork.IsLimit.ofι
  signature: {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
  body: isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition

中文:
定义 核叉.是极限.ofι
  签名: {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
  定义体: isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition

Depends on / 依赖: condition, isLimitAux, s.condition
-/
def KernelFork.IsLimit.ofι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
    (lift : forall {W' : C} (g' : W' ⟶ X) (_ : g' ≫ f = 0), W' ⟶ W)
    (fac : forall {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
    (uniq :
      forall {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (_ : m ≫ g = g'), m = lift g' eq') :
    IsLimit (KernelFork.ofι g eq) :=
  isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition

/--
Definition of `KernelFork.IsLimit.ofι'` / `KernelFork.IsLimit.ofι'` 的定义

English:
definition KernelFork.IsLimit.ofι'
  signature: {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
  body: ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i]; rw [(h k hk).2]; rw [hm])

中文:
定义 核叉.是极限.ofι'
  签名: {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
  定义体: ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i]; rw [(h k hk).2]; rw [hm])

Depends on / 依赖: BraidedCategory, IsCommMonObj, IsMonHom, cancel_mono
-/
def KernelFork.IsLimit.ofι' {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
    (h : forall {A : C} (k : A ⟶ X) (_ : k ≫ f = 0), { l : A ⟶ K // l ≫ i = k}) [hi : Mono i] :
    IsLimit (KernelFork.ofι i w) :=
  ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i]; rw [(h k hk).2]; rw [hm])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isKernelCompMono` / `isKernelCompMono` 的定义

English:
definition isKernelCompMono
  signature: {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
  body: Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

中文:
定义 isKernelCompMono
  签名: {c : 核叉 f} (i : 是极限 c) {Z} (g : Y ⟶ Z) [hg : 单态射 g] {h : X ⟶ Z}
  定义体: Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.mk, Fork.of, IsLimit, KernelFork, KernelFork.IsLimit.lift, cancel_mono, condition, hom_ext, s.condition
-/
def isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
    (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]) : KernelFork h) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

/--
theorem `isKernelCompMono_lift` / 定理 `isKernelCompMono_lift`

English:
theorem isKernelCompMono_lift
  statement: {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
  proof: rfl

中文:
定理 isKernelCompMono_lift
  结论: {c : 核叉 f} (i : 是极限 c) {Z} (g : Y ⟶ Z) [hg : 单态射 g]
  证明: rfl
-/
theorem isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
    {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) :
    (isKernelCompMono i g hh).lift s = i.lift (Fork.ofι s.ι (by
      rw [← cancel_mono g]; rw [Category.assoc]; rw [← hh]
      simp)) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isKernelOfComp` / `isKernelOfComp` 的定义

English:
definition isKernelOfComp
  signature: {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
  body: Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

中文:
定义 isKernelOfComp
  签名: {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : 核叉 h} (i : 是极限 c)
  定义体: Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.lift_, Fork.IsLimit.mk, IsLimit, KernelFork, KernelFork.of, hom_ext, i.lift
-/
def isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
    (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf) :=
  Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

/--
Definition of `KernelFork.IsLimit.ofId` / `KernelFork.IsLimit.ofId` 的定义

English:
definition KernelFork.IsLimit.ofId
  signature: {X Y : C} (f : X ⟶ Y) (hf : f = 0)
  body: KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

中文:
定义 核叉.是极限.ofId
  签名: {X Y : C} (f : X ⟶ Y) (hf : f = 0)
  定义体: KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

Depends on / 依赖: Category, Category.comp_id, IsLimit, KernelFork, KernelFork.IsLimit.of, comp_id
-/
def KernelFork.IsLimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

/--
Definition of `KernelFork.IsLimit.ofMonoOfIsZero` / `KernelFork.IsLimit.ofMonoOfIsZero` 的定义

English:
definition KernelFork.IsLimit.ofMonoOfIsZero
  signature: {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  body: isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

中文:
定义 核叉.是极限.ofMonoOfIsZero
  签名: {X Y : C} {f : X ⟶ Y} (c : 核叉 f)
  定义体: isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

Depends on / 依赖: cancel_mono, condition, eq_of_tgt, h.eq_of_tgt, isLimitAux, s.condition, zero_comp
-/
def KernelFork.IsLimit.ofMonoOfIsZero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

/--
lemma `KernelFork.IsLimit.isIso_ι` / 引理 `KernelFork.IsLimit.isIso_ι`

English:
lemma KernelFork.IsLimit.isIso_ι
  statement: {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  proof: isIso_limit_cone_parallelPair_of_eq hf hc

中文:
引理 核叉.是极限.isIso_ι
  结论: {X Y : C} {f : X ⟶ Y} (c : 核叉 f)
  证明: isIso_limit_cone_parallelPair_of_eq hf hc

Depends on / 依赖: isIso_limit_cone_parallelPair_of_eq
-/
lemma KernelFork.IsLimit.isIso_ι {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := isIso_limit_cone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `KernelFork.isLimitOfIsLimitOfIff` / `KernelFork.isLimitOfIsLimitOfIff` 的定义

English:
definition KernelFork.isLimitOfIsLimitOfIff
  signature: {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
  body: KernelFork.IsLimit.ofι _ _
    (fun s hs => hc.lift (KernelFork.ofι (ι := s ≫ e.inv)
      (by rw [iff, Category.assoc, Iso.inv_hom_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Fork.IsLimit.hom_ext hc (by simpa [← cancel_mono e.hom] using hm))

中文:
定义 核叉.isLimitOfIsLimitOfIff
  签名: {X Y : C} {g : X ⟶ Y} {c : 核叉 g} (hc : 是极限 c)
  定义体: KernelFork.IsLimit.ofι _ _
    (fun s hs => hc.lift (KernelFork.ofι (ι := s ≫ e.inv)
      (by rw [iff, Category.assoc, Iso.inv_hom_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Fork.IsLimit.hom_ext hc (by simpa [← cancel_mono e.hom] using hm))

Depends on / 依赖: e.hom
-/
def KernelFork.isLimitOfIsLimitOfIff {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {X' Y' : C} (g' : X' ⟶ Y') (e : X ≅ X')
    (iff : forall ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') (c.ι ≫ e.hom) (by simp [← iff])) :=
  KernelFork.IsLimit.ofι _ _
    (fun s hs => hc.lift (KernelFork.ofι (ι := s ≫ e.inv)
      (by rw [iff, Category.assoc, Iso.inv_hom_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Fork.IsLimit.hom_ext hc (by simpa [← cancel_mono e.hom] using hm))

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `KernelFork.isLimitOfIsLimitOfIff'` / `KernelFork.isLimitOfIsLimitOfIff'` 的定义

English:
definition KernelFork.isLimitOfIsLimitOfIff'
  signature: {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
  body: IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))

中文:
定义 核叉.isLimitOfIsLimitOfIff'
  签名: {X Y : C} {g : X ⟶ Y} {c : 核叉 g} (hc : 是极限 c)
  定义体: IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))
-/
def KernelFork.isLimitOfIsLimitOfIff' {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {Y' : C} (g' : X ⟶ Y')
    (iff : forall ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') c.ι (by simp [← iff])) :=
  IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))

/--
lemma `KernelFork.IsLimit.isZero_of_mono` / 引理 `KernelFork.IsLimit.isZero_of_mono`

English:
lemma KernelFork.IsLimit.isZero_of_mono
  statement: {X Y : C} {f : X ⟶ Y}
  proof: by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono c.ι]; rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [c.condition]; rw [comp_zero]; rw [zero_comp]

中文:
引理 核叉.是极限.isZero_of_mono
  结论: {X Y : C} {f : X ⟶ Y}
  证明: by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono c.ι]; rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [c.condition]; rw [comp_zero]; rw [zero_comp]

Depends on / 依赖: Category, Category.assoc, Fork.IsLimit.mono, IsLimit, IsZero, IsZero.iff_id_eq_zero, c.condition, cancel_mono, comp_zero, condition, iff_id_eq_zero, zero_comp
-/
lemma KernelFork.IsLimit.isZero_of_mono {X Y : C} {f : X ⟶ Y}
    {c : KernelFork f} (hc : IsLimit c) [Mono f] : IsZero c.pt := by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono c.ι]; rw [← cancel_mono f]; rw [Category.assoc]; rw [Category.assoc]; rw [c.condition]; rw [comp_zero]; rw [zero_comp]

end

namespace KernelFork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapOfIsLimit` / `mapOfIsLimit` 的定义

English:
definition mapOfIsLimit
  signature: (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
  body: hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

#adaptation_note

中文:
定义 mapOfIsLimit
  签名: (kf : 核叉 f) {kf' : 核叉 f'} (hf' : 是极限 kf')
  定义体: hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

#adaptation_note

Depends on / 依赖: KernelFork, KernelFork.of
-/
def mapOfIsLimit (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : kf.pt ⟶ kf'.pt :=
  hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `mapOfIsLimit_ι` / 引理 `mapOfIsLimit_ι`

English:
lemma mapOfIsLimit_ι
  statement: (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
  proof: hf'.fac _ _

中文:
引理 mapOfIsLimit_ι
  结论: (kf : 核叉 f) {kf' : 核叉 f'} (hf' : 是极限 kf')
  证明: hf'.fac _ _
-/
lemma mapOfIsLimit_ι (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    kf.mapOfIsLimit hf' φ ≫ kf'.ι = kf.ι ≫ φ.left :=
  hf'.fac _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of limit kernel forks induced by an isomorphism
in the category of arrows. -/
@[simps]
/--
Definition of `mapIsoOfIsLimit` / `mapIsoOfIsLimit` 的定义

English:
definition mapIsoOfIsLimit
  signature: {kf : KernelFork f} {kf' : KernelFork f'}
  body: kf.mapOfIsLimit hf' φ.hom
  inv := kf'.mapOfIsLimit hf φ.inv
  hom_inv_id := Fork.IsLimit.hom_ext hf (by simp)
  inv_hom_id := Fork.IsLimit.hom_ext hf' (by simp)

中文:
定义 mapIsoOfIsLimit
  签名: {kf : 核叉 f} {kf' : 核叉 f'}
  定义体: kf.mapOfIsLimit hf' φ.hom
  inv := kf'.mapOfIsLimit hf φ.inv
  hom_inv_id := Fork.IsLimit.hom_ext hf (by simp)
  inv_hom_id := Fork.IsLimit.hom_ext hf' (by simp)

Depends on / 依赖: kf.mapOfIsLimit, mapOfIsLimit
-/
def mapIsoOfIsLimit {kf : KernelFork f} {kf' : KernelFork f'}
    (hf : IsLimit kf) (hf' : IsLimit kf')
    (φ : Arrow.mk f ≅ Arrow.mk f') : kf.pt ≅ kf'.pt where
  hom := kf.mapOfIsLimit hf' φ.hom
  inv := kf'.mapOfIsLimit hf φ.inv
  hom_inv_id := Fork.IsLimit.hom_ext hf (by simp)
  inv_hom_id := Fork.IsLimit.hom_ext hf' (by simp)

end KernelFork

section

variable [HasKernel f]

/--
Definition of `kernel` / `kernel` 的定义

English:
abbreviation kernel
  signature: (f : X ⟶ Y) [HasKernel f]
  body: equalizer f 0

中文:
缩写 kernel
  签名: (f : X ⟶ Y) [HasKernel f]
  定义体: equalizer f 0

Depends on / 依赖: equalizer
-/
abbrev kernel (f : X ⟶ Y) [HasKernel f] : C :=
  equalizer f 0

/--
Definition of `kernel.ι` / `kernel.ι` 的定义

English:
abbreviation kernel.ι
  signature: : kernel f ⟶ X
  body: equalizer.ι f 0

@[simp]

中文:
缩写 kernel.ι
  签名: : kernel f ⟶ X
  定义体: equalizer.ι f 0

@[simp]

Depends on / 依赖: equalizer
-/
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0

@[simp]
/--
theorem `equalizer_as_kernel` / 定理 `equalizer_as_kernel`

English:
theorem equalizer_as_kernel
  statement: equalizer.ι f 0 = kernel.ι f
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 equalizer_as_kernel
  结论: equalizer.ι f 0 = kernel.ι f
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f := rfl

@[reassoc (attr := simp)]
/--
theorem `kernel.condition` / 定理 `kernel.condition`

English:
theorem kernel.condition
  statement: kernel.ι f ≫ f = 0
  proof: KernelFork.condition _

中文:
定理 kernel.condition
  结论: kernel.ι f ≫ f = 0
  证明: KernelFork.condition _

Depends on / 依赖: KernelFork, KernelFork.condition, condition
-/
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `kernelIsKernel` / `kernelIsKernel` 的定义

English:
definition kernelIsKernel
  signature: : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm))
  body: IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

中文:
定义 kernelIsKernel
  签名: : 是极限 (叉.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm))
  定义体: IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, isLimit, limit.isLimit, ofIsoLimit
-/
def kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

/--
Definition of `kernel.lift` / `kernel.lift` 的定义

English:
abbreviation kernel.lift
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  body: (kernelIsKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]

中文:
缩写 kernel.lift
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  定义体: (kernelIsKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of, kernelIsKernel
-/
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  (kernelIsKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
/--
theorem `kernel.lift_ι` / 定理 `kernel.lift_ι`

English:
theorem kernel.lift_ι
  given: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  statement: kernel.lift f k h ≫ kernel.ι f = k
  proof: (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[simp]

中文:
定理 kernel.lift_ι
  条件: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  结论: kernel.lift f k h ≫ kernel.ι f = k
  证明: (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[simp]

Depends on / 依赖: KernelFork, KernelFork.of, WalkingParallelPair, WalkingParallelPair.zero, kernelIsKernel
-/
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[simp]
/--
theorem `kernel.lift_zero` / 定理 `kernel.lift_zero`

English:
theorem kernel.lift_zero
  given: {W : C} {h}
  statement: kernel.lift f (0 : W ⟶ X) h = 0
  proof: by
  ext; simp

中文:
定理 kernel.lift_zero
  条件: {W : C} {h}
  结论: kernel.lift f (0 : W ⟶ X) h = 0
  证明: by
  ext; simp
-/
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by
  ext; simp

/--
Instance `kernel.lift_mono` / 实例 `kernel.lift_mono`

English:
instance kernel.lift_mono
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k]
  body: ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

中文:
实例 kernel.lift_mono
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [单态射 k]
  定义体: ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

Depends on / 依赖: Category, Category.assoc, cancel_mono, kernel, kernel.lift_, replace
-/
instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

/--
Definition of `kernel.lift'` / `kernel.lift'` 的定义

English:
definition kernel.lift'
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  body: ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

中文:
定义 kernel.lift'
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  定义体: ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

Depends on / 依赖: kernel, kernel.lift, kernel.lift_
-/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/--
Definition of `kernel.map` / `kernel.map` 的定义

English:
abbreviation kernel.map
  signature: {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
  body: kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[simp]

中文:
缩写 kernel.map
  签名: {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
  定义体: kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[simp]

Depends on / 依赖: kernel, kernel.lift
-/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[simp]
/--
lemma `kernel.map_id` / 引理 `kernel.map_id`

English:
lemma kernel.map_id
  statement: {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
  proof: by
  cat_disch

中文:
引理 kernel.map_id
  结论: {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma kernel.map_id {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  cat_disch

instance {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [IsIso p] [Mono q] :
    IsIso (kernel.map _ _ _ _ w) :=
  ⟨kernel.lift _ (kernel.ι f' ≫ inv p) (by simp [← cancel_mono q, w]),
    by cat_disch, by cat_disch⟩

/--
theorem `kernel.lift_map` / 定理 `kernel.lift_map`

English:
theorem kernel.lift_map
  statement: {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
  proof: by
  ext; simp [h₁]

@[simp]

中文:
定理 kernel.lift_map
  结论: {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
  证明: by
  ext; simp [h₁]

@[simp]
-/
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext; simp [h₁]

@[simp]
/--
lemma `kernel.map_zero` / 引理 `kernel.map_zero`

English:
lemma kernel.map_zero
  statement: {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
  proof: by
  cat_disch

中文:
引理 kernel.map_zero
  结论: {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma kernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
    (q : Y ⟶ Y') (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of kernels. -/
@[simps]
/--
Definition of `kernel.mapIso` / `kernel.mapIso` 的定义

English:
definition kernel.mapIso
  signature: {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
  body: kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

中文:
定义 kernel.mapIso
  签名: {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
  定义体: kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

Depends on / 依赖: kernel, kernel.map, p.hom, q.hom
-/
def kernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : kernel f ≅ kernel f' where
  hom := kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

/--
Instance `kernel.ι_zero_isIso` / 实例 `kernel.ι_zero_isIso`

English:
instance kernel.ι_zero_isIso
  signature: : IsIso (kernel.ι (0 : X ⟶ Y))
  body: equalizer.ι_of_self _

中文:
实例 kernel.ι_zero_isIso
  签名: : 是同构 (kernel.ι (0 : X ⟶ Y))
  定义体: equalizer.ι_of_self _

Depends on / 依赖: equalizer
-/
instance kernel.ι_zero_isIso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

/--
theorem `eq_zero_of_epi_kernel` / 定理 `eq_zero_of_epi_kernel`

English:
theorem eq_zero_of_epi_kernel
  given: [Epi (kernel.ι f)]
  statement: f = 0
  proof: (cancel_epi (kernel.ι f)).1 (by simp)

中文:
定理 eq_zero_of_epi_kernel
  条件: [满态射 (kernel.ι f)]
  结论: f = 0
  证明: (cancel_epi (kernel.ι f)).1 (by simp)

Depends on / 依赖: cancel_epi, kernel
-/
theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1 (by simp)

/--
Definition of `kernelZeroIsoSource` / `kernelZeroIsoSource` 的定义

English:
definition kernelZeroIsoSource
  signature: : kernel (0 : X ⟶ Y) ≅ X
  body: equalizer.isoSourceOfSelf 0

@[simp]

中文:
定义 kernelZeroIsoSource
  签名: : kernel (0 : X ⟶ Y) ≅ X
  定义体: equalizer.isoSourceOfSelf 0

@[simp]

Depends on / 依赖: equalizer, equalizer.isoSourceOfSelf, isoSourceOfSelf
-/
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0

@[simp]
/--
theorem `kernelZeroIsoSource_hom` / 定理 `kernelZeroIsoSource_hom`

English:
theorem kernelZeroIsoSource_hom
  statement: kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y)
  proof: rfl

中文:
定理 kernelZeroIsoSource_hom
  结论: kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y)
  证明: rfl
-/
theorem kernelZeroIsoSource_hom : kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `kernelZeroIsoSource_inv` / 定理 `kernelZeroIsoSource_inv`

English:
theorem kernelZeroIsoSource_inv
  proof: by
  ext
  simp [kernelZeroIsoSource]

中文:
定理 kernelZeroIsoSource_inv
  证明: by
  ext
  simp [kernelZeroIsoSource]

Depends on / 依赖: kernelZeroIsoSource
-/
theorem kernelZeroIsoSource_inv :
    kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) := by
  ext
  simp [kernelZeroIsoSource]

/--
Definition of `kernelIsoOfEq` / `kernelIsoOfEq` 的定义

English:
definition kernelIsoOfEq
  signature: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  body: HasLimit.isoOfNatIso (by rw [h])

中文:
定义 kernelIsoOfEq
  签名: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  定义体: HasLimit.isoOfNatIso (by rw [h])

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, isoOfNatIso
-/
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso (by rw [h])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `kernelIsoOfEq_refl` / 定理 `kernelIsoOfEq_refl`

English:
theorem kernelIsoOfEq_refl
  given: {h : f = f}
  statement: kernelIsoOfEq h = Iso.refl (kernel f)
  proof: by
  ext
  simp [kernelIsoOfEq]

@[reassoc (attr := simp)]

中文:
定理 kernelIsoOfEq_refl
  条件: {h : f = f}
  结论: kernelIsoOfEq h = 同构.refl (kernel f)
  证明: by
  ext
  simp [kernelIsoOfEq]

@[reassoc (attr := simp)]

Depends on / 依赖: kernelIsoOfEq
-/
theorem kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by
  ext
  simp [kernelIsoOfEq]

@[reassoc (attr := simp)]
/--
theorem `kernelIsoOfEq_hom_comp_ι` / 定理 `kernelIsoOfEq_hom_comp_ι`

English:
theorem kernelIsoOfEq_hom_comp_ι
  given: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  proof: by
  subst h; simp

@[reassoc (attr := simp)]

中文:
定理 kernelIsoOfEq_hom_comp_ι
  条件: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  证明: by
  subst h; simp

@[reassoc (attr := simp)]
-/
theorem kernelIsoOfEq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).hom ≫ kernel.ι g = kernel.ι f := by
  subst h; simp

@[reassoc (attr := simp)]
/--
theorem `kernelIsoOfEq_inv_comp_ι` / 定理 `kernelIsoOfEq_inv_comp_ι`

English:
theorem kernelIsoOfEq_inv_comp_ι
  given: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  proof: by
  subst h; simp

@[reassoc (attr := simp)]

中文:
定理 kernelIsoOfEq_inv_comp_ι
  条件: {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  证明: by
  subst h; simp

@[reassoc (attr := simp)]
-/
theorem kernelIsoOfEq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by
  subst h; simp

@[reassoc (attr := simp)]
/--
theorem `lift_comp_kernelIsoOfEq_hom` / 定理 `lift_comp_kernelIsoOfEq_hom`

English:
theorem lift_comp_kernelIsoOfEq_hom
  statement: {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  proof: by
  subst h; simp

@[reassoc (attr := simp)]

中文:
定理 lift_comp_kernelIsoOfEq_hom
  结论: {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  证明: by
  subst h; simp

@[reassoc (attr := simp)]
-/
theorem lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).hom = kernel.lift _ e (by simp [← h, he]) := by
  subst h; simp

@[reassoc (attr := simp)]
/--
theorem `lift_comp_kernelIsoOfEq_inv` / 定理 `lift_comp_kernelIsoOfEq_inv`

English:
theorem lift_comp_kernelIsoOfEq_inv
  statement: {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  proof: by
  cases h; simp

@[simp]

中文:
定理 lift_comp_kernelIsoOfEq_inv
  结论: {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
  证明: by
  cases h; simp

@[simp]
-/
theorem lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kernel.lift _ e (by simp [h, he]) := by
  cases h; simp

@[simp]
/--
theorem `kernelIsoOfEq_trans` / 定理 `kernelIsoOfEq_trans`

English:
theorem kernelIsoOfEq_trans
  statement: {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
  proof: by
  cases w₁; simp

中文:
定理 kernelIsoOfEq_trans
  结论: {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
  证明: by
  cases w₁; simp
-/
theorem kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
    (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}

/--
theorem `kernel_not_epi_of_nonzero` / 定理 `kernel_not_epi_of_nonzero`

English:
theorem kernel_not_epi_of_nonzero
  given: (w : f != 0)
  statement: ¬Epi (kernel.ι f)
  proof: fun _ =>
  w (eq_zero_of_epi_kernel f)

中文:
定理 kernel_not_epi_of_nonzero
  条件: (w : f != 0)
  结论: ¬满态射 (kernel.ι f)
  证明: fun _ =>
  w (eq_zero_of_epi_kernel f)
-/
theorem kernel_not_epi_of_nonzero (w : f != 0) : ¬Epi (kernel.ι f) := fun _ =>
  w (eq_zero_of_epi_kernel f)

/--
theorem `kernel_not_iso_of_nonzero` / 定理 `kernel_not_iso_of_nonzero`

English:
theorem kernel_not_iso_of_nonzero
  given: (w : f != 0)
  statement: IsIso (kernel.ι f) -> False
  proof: fun _ =>
  kernel_not_epi_of_nonzero w inferInstance

中文:
定理 kernel_not_iso_of_nonzero
  条件: (w : f != 0)
  结论: 是同构 (kernel.ι f) -> 假
  证明: fun _ =>
  kernel_not_epi_of_nonzero w inferInstance
-/
theorem kernel_not_iso_of_nonzero (w : f != 0) : IsIso (kernel.ι f) -> False := fun _ =>
  kernel_not_epi_of_nonzero w inferInstance

/--
Instance `hasKernel_comp_mono` / 实例 `hasKernel_comp_mono`

English:
instance hasKernel_comp_mono
  signature: {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g]
  body: ⟨⟨{ cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

中文:
实例 hasKernel_comp_mono
  签名: {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [单态射 g]
  定义体: ⟨⟨{ cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

Depends on / 依赖: isKernelCompMono, isLimit, limit.isLimit
-/
instance hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] :
    HasKernel (f ≫ g) :=
  ⟨⟨{ cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
/--
Definition of `kernelCompMono` / `kernelCompMono` 的定义

English:
definition kernelCompMono
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g]
  body: kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

中文:
定义 kernelCompMono
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [单态射 g]
  定义体: kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

Depends on / 依赖: cancel_mono, kernel, kernel.lift
-/
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] :
    kernel (f ≫ g) ≅ kernel f where
  hom :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `hasKernel_iso_comp` / 实例 `hasKernel_iso_comp`

English:
instance hasKernel_iso_comp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g]
  body: ⟨{ cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

中文:
实例 hasKernel_iso_comp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [是同构 f] [HasKernel g]
  定义体: ⟨{ cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

Depends on / 依赖: KernelFork, KernelFork.of, equalizer, equalizer.hom_ext, hom_ext, isLimit, isLimitAux, kernel, kernel.lift, simp_rw
-/
instance hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{ cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
/--
Definition of `kernelIsIsoComp` / `kernelIsIsoComp` 的定义

English:
definition kernelIsIsoComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g]
  body: kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

@[deprecated (since := "2026-07-03")] alias kernel.congr := kernelIsoOfEq

中文:
定义 kernelIsIsoComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [是同构 f] [HasKernel g]
  定义体: kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

@[deprecated (since := "2026-07-03")] alias kernel.congr := kernelIsoOfEq

Depends on / 依赖: kernel, kernel.lift
-/
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    kernel (f ≫ g) ≅ kernel g where
  hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

@[deprecated (since := "2026-07-03")] alias kernel.congr := kernelIsoOfEq

/--
lemma `isZero_kernel_of_mono` / 引理 `isZero_kernel_of_mono`

English:
lemma isZero_kernel_of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f]
  proof: KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

中文:
引理 isZero_kernel_of_mono
  条件: {X Y : C} (f : X ⟶ Y) [单态射 f] [HasKernel f]
  证明: KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.isZero_of_mono, KernelFork.of, condition, isZero_of_mono, kernel, kernel.condition, kernelIsKernel
-/
lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) :=
  KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism from the zero object determines a cone on a kernel diagram -/
@[simps! pt]
/--
Definition of `kernel.zeroKernelFork` / `kernel.zeroKernelFork` 的定义

English:
definition kernel.zeroKernelFork
  signature: : KernelFork f
  body: KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[simp]

中文:
定义 kernel.zeroKernelFork
  签名: : 核叉 f
  定义体: KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[simp]

Depends on / 依赖: KernelFork, KernelFork.of, zero_comp
-/
def kernel.zeroKernelFork : KernelFork f :=
  KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[simp]
/--
lemma `kernel.zeroKernelFork_ι` / 引理 `kernel.zeroKernelFork_ι`

English:
lemma kernel.zeroKernelFork_ι
  statement: (kernel.zeroKernelFork f).ι = 0
  proof: rfl

中文:
引理 kernel.zeroKernelFork_ι
  结论: (kernel.zeroKernelFork f).ι = 0
  证明: rfl
-/
lemma kernel.zeroKernelFork_ι : (kernel.zeroKernelFork f).ι = 0 := rfl

/--
Definition of `kernel.isLimitConeZeroCone` / `kernel.isLimitConeZeroCone` 的定义

English:
definition kernel.isLimitConeZeroCone
  signature: [Mono f]
  body: Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

中文:
定义 kernel.isLimitConeZeroCone
  签名: [单态射 f]
  定义体: Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

Depends on / 依赖: Fork.IsLimit.mk, IsLimit, KernelFork, KernelFork.condition, condition, zero_comp, zero_of_comp_mono, zero_of_to_zero
-/
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroKernelFork f) :=
  Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

/--
Definition of `kernel.ofMono` / `kernel.ofMono` 的定义

English:
definition kernel.ofMono
  signature: [HasKernel f] [Mono f]
  body: Functor.mapIso (Cone.forget _)
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

中文:
定义 kernel.ofMono
  签名: [HasKernel f] [单态射 f]
  定义体: Functor.mapIso (Cone.forget _)
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

Depends on / 依赖: Cone.forget, Functor, Functor.mapIso, IsLimit, IsLimit.uniqueUpToIso, forget, isLimit, isLimitConeZeroCone, kernel, kernel.isLimitConeZeroCone, limit.isLimit, mapIso, parallelPair, uniqueUpToIso
-/
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
Functor.mapIso (Cone.forget _)
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

/--
theorem `kernel.ι_of_mono` / 定理 `kernel.ι_of_mono`

English:
theorem kernel.ι_of_mono
  given: [HasKernel f] [Mono f]
  statement: kernel.ι f = 0
  proof: zero_of_source_iso_zero _ (kernel.ofMono f)

中文:
定理 kernel.ι_of_mono
  条件: [HasKernel f] [单态射 f]
  结论: kernel.ι f = 0
  证明: zero_of_source_iso_zero _ (kernel.ofMono f)

Depends on / 依赖: kernel, kernel.ofMono, ofMono, zero_of_source_iso_zero
-/
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)

/--
Definition of `zeroKernelOfCancelZero` / `zeroKernelOfCancelZero` 的定义

English:
definition zeroKernelOfCancelZero
  signature: {X Y : C} (f : X ⟶ Y)
  body: Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by apply HasZeroObject.to_zero_ext

中文:
定义 zeroKernelOfCancelZero
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by apply HasZeroObject.to_zero_ext

Depends on / 依赖: Fork.IsLimit.mk, HasZeroObject, HasZeroObject.to_zero_ext, IsLimit, KernelFork, KernelFork.condition, condition, to_zero_ext, zero_comp
-/
def zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y)
    (hf : forall (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) :
    IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 0 by simp)) :=
  Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by apply HasZeroObject.to_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsKernel.ofIso` / `IsKernel.ofIso` 的定义

English:
definition IsKernel.ofIso
  signature: {X' Y' : C} {f' : X' ⟶ Y'} {s : KernelFork f} (hs : IsLimit s)
  body: let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs)
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

中文:
定义 IsKernel.ofIso
  签名: {X' Y' : C} {f' : X' ⟶ Y'} {s : 核叉 f} (hs : 是极限 s)
  定义体: let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs)
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

Depends on / 依赖: Cone.ext, H.symm, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, ofIsoLimit, parallelPair, parallelPairIsoMk, postcomposeHomEquiv
-/
def IsKernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : KernelFork f} (hs : IsLimit s)
    (s' : KernelFork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : e.hom ≫ s'.ι = s.ι ≫ eX.hom) :
    IsLimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs)
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsKernel.ofCompIso` / `IsKernel.ofCompIso` 的定义

English:
definition IsKernel.ofCompIso
  signature: {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) {s : KernelFork f}
  body: Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Fork.IsLimit.hom_ext hs
      simpa using h

中文:
定义 IsKernel.ofCompIso
  签名: {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) {s : 核叉 f}
  定义体: Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Fork.IsLimit.hom_ext hs
      simpa using h

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.mk, IsLimit, KernelFork, KernelFork.of, hom_ext, hs.lift
-/
def IsKernel.ofCompIso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) {s : KernelFork f}
    (hs : IsLimit s) :
    IsLimit
      (KernelFork.ofι (Fork.ι s) <| show Fork.ι s ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Fork.IsLimit.hom_ext hs
      simpa using h

/--
Definition of `kernel.ofCompIso` / `kernel.ofCompIso` 的定义

English:
definition kernel.ofCompIso
  signature: [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f)
  body: IsKernel.ofCompIso f l i h limit.isLimit _

中文:
定义 kernel.ofCompIso
  签名: [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f)
  定义体: IsKernel.ofCompIso f l i h limit.isLimit _

Depends on / 依赖: IsKernel, IsKernel.ofCompIso, isLimit, limit.isLimit, ofCompIso
-/
def kernel.ofCompIso [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) :
    IsLimit
      (KernelFork.ofι (kernel.ι f) <| show kernel.ι f ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
IsKernel.ofCompIso f l i h limit.isLimit _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsKernel.isoKernel` / `IsKernel.isoKernel` 的定义

English:
definition IsKernel.isoKernel
  signature: {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.pt)
  body: IsLimit.ofIsoLimit hs
    Cone.ext i.symm fun j => by
      cases j
      · exact (Iso.eq_inv_comp i).2 h
      · dsimp; rw [← h]; simp

中文:
定义 IsKernel.isoKernel
  签名: {Z : C} (l : Z ⟶ X) {s : 核叉 f} (hs : 是极限 s) (i : Z ≅ s.pt)
  定义体: IsLimit.ofIsoLimit hs
    Cone.ext i.symm fun j => by
      cases j
      · exact (Iso.eq_inv_comp i).2 h
      · dsimp; rw [← h]; simp

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.eq_inv_comp, eq_inv_comp, i.symm, ofIsoLimit
-/
def IsKernel.isoKernel {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.pt)
    (h : i.hom ≫ Fork.ι s = l) : IsLimit (KernelFork.ofι l <| show l ≫ f = 0 by simp [← h]) :=
IsLimit.ofIsoLimit hs
    Cone.ext i.symm fun j => by
      cases j
      · exact (Iso.eq_inv_comp i).2 h
      · dsimp; rw [← h]; simp

/--
Definition of `kernel.isoKernel` / `kernel.isoKernel` 的定义

English:
definition kernel.isoKernel
  signature: [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
  body: IsKernel.isoKernel f l (limit.isLimit _) i h

中文:
定义 kernel.isoKernel
  签名: [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
  定义体: IsKernel.isoKernel f l (limit.isLimit _) i h

Depends on / 依赖: IsKernel, IsKernel.isoKernel, isLimit, isoKernel, limit.isLimit
-/
def kernel.isoKernel [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
    (h : i.hom ≫ kernel.ι f = l) :
    IsLimit (@KernelFork.ofι _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsKernel.isoKernel f l (limit.isLimit _) i h

end Transport

section

/--
theorem `kernel.ι_of_zero` / 定理 `kernel.ι_of_zero`

English:
theorem kernel.ι_of_zero
  given: {f : X ⟶ Y} [HasKernel f] (eq : f = 0)
  proof: equalizer.ι_of_eq eq

中文:
定理 kernel.ι_of_zero
  条件: {f : X ⟶ Y} [HasKernel f] (eq : f = 0)
  证明: equalizer.ι_of_eq eq

Depends on / 依赖: equalizer
-/
theorem kernel.ι_of_zero {f : X ⟶ Y} [HasKernel f] (eq : f = 0) :
    IsIso (kernel.ι f) := equalizer.ι_of_eq eq

end

section

/--
Definition of `CokernelCofork` / `CokernelCofork` 的定义

English:
abbreviation CokernelCofork
  body: Cofork f 0

中文:
缩写 余核余叉
  定义体: Cofork f 0

Depends on / 依赖: Cofork
-/
abbrev CokernelCofork :=
  Cofork f 0

variable {f}

@[reassoc (attr := simp)]
/--
theorem `CokernelCofork.condition` / 定理 `CokernelCofork.condition`

English:
theorem CokernelCofork.condition
  given: (s : CokernelCofork f)
  statement: f ≫ s.π = 0
  proof: by
  rw [Cofork.condition]; rw [zero_comp]

中文:
定理 余核余叉.condition
  条件: (s : 余核余叉 f)
  结论: f ≫ s.π = 0
  证明: by
  rw [Cofork.condition]; rw [zero_comp]

Depends on / 依赖: Cofork, Cofork.condition, condition, zero_comp
-/
theorem CokernelCofork.condition (s : CokernelCofork f) : f ≫ s.π = 0 := by
  rw [Cofork.condition]; rw [zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `CokernelCofork.π_eq_zero` / 定理 `CokernelCofork.π_eq_zero`

English:
theorem CokernelCofork.π_eq_zero
  given: (s : CokernelCofork f)
  statement: s.ι.app zero = 0
  proof: by
  simp

中文:
定理 余核余叉.π_eq_zero
  条件: (s : 余核余叉 f)
  结论: s.ι.app zero = 0
  证明: by
  simp

Depends on / 依赖: infer_instance
-/
theorem CokernelCofork.π_eq_zero (s : CokernelCofork f) : s.ι.app zero = 0 := by
  simp

/--
Definition of `CokernelCofork.ofπ` / `CokernelCofork.ofπ` 的定义

English:
abbreviation CokernelCofork.ofπ
  signature: {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0)
  body: Cofork.ofπ π by rw [w, zero_comp]

@[simp]

中文:
缩写 余核余叉.ofπ
  签名: {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0)
  定义体: Cofork.ofπ π by rw [w, zero_comp]

@[simp]

Depends on / 依赖: Cofork, Cofork.of, infer_instance, zero_comp
-/
abbrev CokernelCofork.ofπ {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : CokernelCofork f :=
Cofork.ofπ π by rw [w, zero_comp]

@[simp]
/--
theorem `CokernelCofork.π_ofπ` / 定理 `CokernelCofork.π_ofπ`

English:
theorem CokernelCofork.π_ofπ
  given: {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0)
  proof: rfl

中文:
定理 余核余叉.π_ofπ
  条件: {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0)
  证明: rfl
-/
theorem CokernelCofork.π_ofπ {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    Cofork.π (CokernelCofork.ofπ π w) = π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoOfπ` / `isoOfπ` 的定义

English:
definition isoOfπ
  signature: (s : Cofork f 0)
  body: Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

中文:
定义 isoOfπ
  签名: (s : 余叉 f 0)
  定义体: Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, cat_disch
-/
def isoOfπ (s : Cofork f 0) : s ≅ Cofork.ofπ (Cofork.π s) (Cofork.condition s) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofπCongr` / `ofπCongr` 的定义

English:
definition ofπCongr
  signature: {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π')
  body: Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

中文:
定义 ofπCongr
  签名: {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π')
  定义体: Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, cat_disch
-/
def ofπCongr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    CokernelCofork.ofπ π w ≅ CokernelCofork.ofπ π' (by rw [← h, w]) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

/--
Definition of `CokernelCofork.IsColimit.desc'` / `CokernelCofork.IsColimit.desc'` 的定义

English:
definition CokernelCofork.IsColimit.desc'
  signature: {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  body: ⟨hs.desc CokernelCofork.ofπ _ h, hs.fac _ _⟩

中文:
定义 余核余叉.是余极限.desc'
  签名: {s : 余核余叉 f} (hs : 是余极限 s) {W : C} (k : Y ⟶ W)
  定义体: ⟨hs.desc CokernelCofork.ofπ _ h, hs.fac _ _⟩

Depends on / 依赖: CokernelCofork, CokernelCofork.of, hs.desc, hs.fac
-/
def CokernelCofork.IsColimit.desc' {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = 0) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
⟨hs.desc CokernelCofork.ofπ _ h, hs.fac _ _⟩

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitAux` / `isColimitAux` 的定义

English:
definition isColimitAux
  signature: (t : CokernelCofork f) (desc : forall s : CokernelCofork f, t.pt ⟶ s.pt)
  body: { desc
    fac := fun s j => by
      cases j
      · simp
      · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

中文:
定义 isColimitAux
  签名: (t : 余核余叉 f) (desc : 对任意 s : 余核余叉 f, t.pt ⟶ s.pt)
  定义体: { desc
    fac := fun s j => by
      cases j
      · simp
      · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

Depends on / 依赖: Limits, Limits.WalkingParallelPair.one, WalkingParallelPair
-/
def isColimitAux (t : CokernelCofork f) (desc : forall s : CokernelCofork f, t.pt ⟶ s.pt)
    (fac : forall s : CokernelCofork f, t.π ≫ desc s = s.π)
    (uniq : forall (s : CokernelCofork f) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j => by
      cases j
      · simp
      · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

/--
Definition of `CokernelCofork.IsColimit.ofπ` / `CokernelCofork.IsColimit.ofπ` 的定义

English:
definition CokernelCofork.IsColimit.ofπ
  signature: {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
  body: isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition

中文:
定义 余核余叉.是余极限.ofπ
  签名: {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
  定义体: isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition

Depends on / 依赖: condition, isColimitAux, s.condition
-/
def CokernelCofork.IsColimit.ofπ {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
    (desc : forall {Z' : C} (g' : Y ⟶ Z') (_ : f ≫ g' = 0), Z ⟶ Z')
    (fac : forall {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
    (uniq :
      forall {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (_ : g ≫ m = g'), m = desc g' eq') :
    IsColimit (CokernelCofork.ofπ g eq) :=
  isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition

/--
Definition of `CokernelCofork.IsColimit.ofπ'` / `CokernelCofork.IsColimit.ofπ'` 的定义

English:
definition CokernelCofork.IsColimit.ofπ'
  signature: {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
  body: ofπ _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p]; rw [(h k hk).2]; rw [hm])

中文:
定义 余核余叉.是余极限.ofπ'
  签名: {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
  定义体: ofπ _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p]; rw [(h k hk).2]; rw [hm])

Depends on / 依赖: cancel_epi
-/
def CokernelCofork.IsColimit.ofπ' {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
    (h : forall {A : C} (k : Y ⟶ A) (_ : f ≫ k = 0), { l : Q ⟶ A // p ≫ l = k}) [hp : Epi p] :
    IsColimit (CokernelCofork.ofπ p w) :=
  ofπ _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p]; rw [(h k hk).2]; rw [hm])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isCokernelEpiComp` / `isCokernelEpiComp` 的定义

English:
definition isCokernelEpiComp
  signature: {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
  body: Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π
        (by
          apply hg.left_cancellation
          rw [← Category.assoc]; rw [← hh]; rw [s.condition]
          simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

@[simp]

中文:
定义 isCokernelEpiComp
  签名: {c : 余核余叉 f} (i : 是余极限 c) {W} (g : W ⟶ X) [hg : 满态射 g]
  定义体: Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π
        (by
          apply hg.left_cancellation
          rw [← Category.assoc]; rw [← hh]; rw [s.condition]
          simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

@[simp]

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, Cofork.of, CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, condition, hg.left_cancellation, hom_ext, left_cancellation, s.condition
-/
def isCokernelEpiComp {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) :
    IsColimit (CokernelCofork.ofπ c.π (by rw [hh]; simp) : CokernelCofork h) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π
        (by
          apply hg.left_cancellation
          rw [← Category.assoc]; rw [← hh]; rw [s.condition]
          simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

@[simp]
/--
theorem `isCokernelEpiComp_desc` / 定理 `isCokernelEpiComp_desc`

English:
theorem isCokernelEpiComp_desc
  statement: {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
  proof: rfl

中文:
定理 isCokernelEpiComp_desc
  结论: {c : 余核余叉 f} (i : 是余极限 c) {W} (g : W ⟶ X) [hg : 满态射 g]
  证明: rfl
-/
theorem isCokernelEpiComp_desc {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) (s : CokernelCofork h) :
    (isCokernelEpiComp i g hh).desc s =
      i.desc
        (Cofork.ofπ s.π
          (by
            rw [← cancel_epi g]; rw [← Category.assoc]; rw [← hh]
            simp)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isCokernelOfComp` / `isCokernelOfComp` 的定义

English:
definition isCokernelOfComp
  signature: {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i : IsColimit c)
  body: Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [CokernelCofork.π_ofπ, Cofork.IsColimit.π_desc]) fun s m h => by
      apply Cofork.IsColimit.hom_ext i
      simpa using h

中文:
定义 isCokernelOfComp
  签名: {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : 余核余叉 h} (i : 是余极限 c)
  定义体: Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [CokernelCofork.π_ofπ, Cofork.IsColimit.π_desc]) fun s m h => by
      apply Cofork.IsColimit.hom_ext i
      simpa using h

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.of, IsColimit, hom_ext, i.desc
-/
def isCokernelOfComp {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i : IsColimit c)
    (hf : f ≫ c.π = 0) (hfg : g ≫ f = h) : IsColimit (CokernelCofork.ofπ c.π hf) :=
  Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [CokernelCofork.π_ofπ, Cofork.IsColimit.π_desc]) fun s m h => by
      apply Cofork.IsColimit.hom_ext i
      simpa using h

/--
Definition of `CokernelCofork.IsColimit.ofId` / `CokernelCofork.IsColimit.ofId` 的定义

English:
definition CokernelCofork.IsColimit.ofId
  signature: {X Y : C} (f : X ⟶ Y) (hf : f = 0)
  body: CokernelCofork.IsColimit.ofπ _ _ (fun x _ => x) (fun _ _ => Category.id_comp _)
    (fun _ _ _ hb => by simp only [← hb, Category.id_comp])

中文:
定义 余核余叉.是余极限.ofId
  签名: {X Y : C} (f : X ⟶ Y) (hf : f = 0)
  定义体: CokernelCofork.IsColimit.ofπ _ _ (fun x _ => x) (fun _ _ => Category.id_comp _)
    (fun _ _ _ hb => by simp only [← hb, Category.id_comp])

Depends on / 依赖: Category, Category.id_comp, CokernelCofork, CokernelCofork.IsColimit.of, IsColimit, id_comp
-/
def CokernelCofork.IsColimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsColimit (CokernelCofork.ofπ (𝟙 Y) (show f ≫ 𝟙 Y = 0 by rw [hf, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun x _ => x) (fun _ _ => Category.id_comp _)
    (fun _ _ _ hb => by simp only [← hb, Category.id_comp])

/--
Definition of `CokernelCofork.IsColimit.ofEpiOfIsZero` / `CokernelCofork.IsColimit.ofEpiOfIsZero` 的定义

English:
definition CokernelCofork.IsColimit.ofEpiOfIsZero
  signature: {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  body: isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

中文:
定义 余核余叉.是余极限.ofEpiOfIsZero
  签名: {X Y : C} {f : X ⟶ Y} (c : 余核余叉 f)
  定义体: isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

Depends on / 依赖: cancel_epi, comp_zero, condition, eq_of_src, h.eq_of_src, isColimitAux, s.condition
-/
def CokernelCofork.IsColimit.ofEpiOfIsZero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

/--
lemma `CokernelCofork.IsColimit.isIso_π` / 引理 `CokernelCofork.IsColimit.isIso_π`

English:
lemma CokernelCofork.IsColimit.isIso_π
  statement: {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  proof: isIso_colimit_cocone_parallelPair_of_eq hf hc

中文:
引理 余核余叉.是余极限.isIso_π
  结论: {X Y : C} {f : X ⟶ Y} (c : 余核余叉 f)
  证明: isIso_colimit_cocone_parallelPair_of_eq hf hc

Depends on / 依赖: isIso_colimit_cocone_parallelPair_of_eq
-/
lemma CokernelCofork.IsColimit.isIso_π {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hc : IsColimit c) (hf : f = 0) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `CokernelCofork.isColimitOfIsColimitOfIff` / `CokernelCofork.isColimitOfIsColimitOfIff` 的定义

English:
definition CokernelCofork.isColimitOfIsColimitOfIff
  signature: {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
  body: CokernelCofork.IsColimit.ofπ _ _
    (fun s hs => hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

中文:
定义 余核余叉.isColimitOfIsColimitOfIff
  签名: {X Y : C} {f : X ⟶ Y} {c : 余核余叉 f}
  定义体: CokernelCofork.IsColimit.ofπ _ _
    (fun s hs => hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

Depends on / 依赖: e.hom
-/
def CokernelCofork.isColimitOfIsColimitOfIff {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' Y' : C} (f' : X' ⟶ Y') (e : Y' ≅ Y)
    (iff : forall ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ c.π) (by simp [← iff])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs => hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs => by simp)
    (fun s hs m hm => Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `CokernelCofork.isColimitOfIsColimitOfIff'` / `CokernelCofork.isColimitOfIsColimitOfIff'` 的定义

English:
definition CokernelCofork.isColimitOfIsColimitOfIff'
  signature: {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
  body: IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff hc f' (Iso.refl _) (by simpa using iff))
    (Cofork.ext (Iso.refl _))

中文:
定义 余核余叉.isColimitOfIsColimitOfIff'
  签名: {X Y : C} {f : X ⟶ Y} {c : 余核余叉 f}
  定义体: IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff hc f' (Iso.refl _) (by simpa using iff))
    (Cofork.ext (Iso.refl _))
-/
def CokernelCofork.isColimitOfIsColimitOfIff' {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' : C} (f' : X' ⟶ Y)
    (iff : forall ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') c.π (by simp [← iff])) :=
  IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff hc f' (Iso.refl _) (by simpa using iff))
    (Cofork.ext (Iso.refl _))

/--
lemma `CokernelCofork.IsColimit.isZero_of_epi` / 引理 `CokernelCofork.IsColimit.isZero_of_epi`

English:
lemma CokernelCofork.IsColimit.isZero_of_epi
  statement: {X Y : C} {f : X ⟶ Y}
  proof: by
  have := Cofork.IsColimit.epi hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi c.π]; rw [← cancel_epi f]; rw [c.condition_assoc]; rw [comp_zero]; rw [comp_zero]; rw [zero_comp]

中文:
引理 余核余叉.是余极限.isZero_of_epi
  结论: {X Y : C} {f : X ⟶ Y}
  证明: by
  have := Cofork.IsColimit.epi hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi c.π]; rw [← cancel_epi f]; rw [c.condition_assoc]; rw [comp_zero]; rw [comp_zero]; rw [zero_comp]

Depends on / 依赖: Cofork, Cofork.IsColimit.epi, IsColimit, IsZero, IsZero.iff_id_eq_zero, c.condition_assoc, cancel_epi, comp_zero, condition_assoc, iff_id_eq_zero, zero_comp
-/
lemma CokernelCofork.IsColimit.isZero_of_epi {X Y : C} {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) [Epi f] : IsZero c.pt := by
  have := Cofork.IsColimit.epi hc
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi c.π]; rw [← cancel_epi f]; rw [c.condition_assoc]; rw [comp_zero]; rw [comp_zero]; rw [zero_comp]

end

namespace CokernelCofork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapOfIsColimit` / `mapOfIsColimit` 的定义

English:
definition mapOfIsColimit
  signature: {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
  body: hf.desc (CokernelCofork.ofπ (φ.right ≫ cc'.π) (by
    erw [← Arrow.w_assoc φ, condition, comp_zero]))

#adaptation_note

中文:
定义 mapOfIsColimit
  签名: {cc : 余核余叉 f} (hf : 是余极限 cc) (cc' : 余核余叉 f')
  定义体: hf.desc (CokernelCofork.ofπ (φ.right ≫ cc'.π) (by
    erw [← Arrow.w_assoc φ, condition, comp_zero]))

#adaptation_note

Depends on / 依赖: Arrow.w_assoc, CokernelCofork, CokernelCofork.of, comp_zero, condition, hf.desc, w_assoc
-/
def mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : cc.pt ⟶ cc'.pt :=
  hf.desc (CokernelCofork.ofπ (φ.right ≫ cc'.π) (by
    erw [← Arrow.w_assoc φ, condition, comp_zero]))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `π_mapOfIsColimit` / 引理 `π_mapOfIsColimit`

English:
lemma π_mapOfIsColimit
  statement: {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
  proof: hf.fac _ _

中文:
引理 π_mapOfIsColimit
  结论: {cc : 余核余叉 f} (hf : 是余极限 cc) (cc' : 余核余叉 f')
  证明: hf.fac _ _

Depends on / 依赖: hf.fac
-/
lemma π_mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    cc.π ≫ mapOfIsColimit hf cc' φ = φ.right ≫ cc'.π :=
  hf.fac _ _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of limit cokernel coforks induced by an isomorphism
in the category of arrows. -/
@[simps]
/--
Definition of `mapIsoOfIsColimit` / `mapIsoOfIsColimit` 的定义

English:
definition mapIsoOfIsColimit
  signature: {cc : CokernelCofork f} {cc' : CokernelCofork f'}
  body: mapOfIsColimit hf cc' φ.hom
  inv := mapOfIsColimit hf' cc φ.inv
  hom_inv_id := Cofork.IsColimit.hom_ext hf (by simp)
  inv_hom_id := Cofork.IsColimit.hom_ext hf' (by simp)

中文:
定义 mapIsoOfIsColimit
  签名: {cc : 余核余叉 f} {cc' : 余核余叉 f'}
  定义体: mapOfIsColimit hf cc' φ.hom
  inv := mapOfIsColimit hf' cc φ.inv
  hom_inv_id := Cofork.IsColimit.hom_ext hf (by simp)
  inv_hom_id := Cofork.IsColimit.hom_ext hf' (by simp)

Depends on / 依赖: mapOfIsColimit
-/
def mapIsoOfIsColimit {cc : CokernelCofork f} {cc' : CokernelCofork f'}
    (hf : IsColimit cc) (hf' : IsColimit cc')
    (φ : Arrow.mk f ≅ Arrow.mk f') : cc.pt ≅ cc'.pt where
  hom := mapOfIsColimit hf cc' φ.hom
  inv := mapOfIsColimit hf' cc φ.inv
  hom_inv_id := Cofork.IsColimit.hom_ext hf (by simp)
  inv_hom_id := Cofork.IsColimit.hom_ext hf' (by simp)

end CokernelCofork

section

variable [HasCokernel f]

/--
Definition of `cokernel` / `cokernel` 的定义

English:
abbreviation cokernel
  signature: : C
  body: coequalizer f 0

中文:
缩写 cokernel
  签名: : C
  定义体: coequalizer f 0

Depends on / 依赖: coequalizer
-/
abbrev cokernel : C :=
  coequalizer f 0

/--
Definition of `cokernel.π` / `cokernel.π` 的定义

English:
abbreviation cokernel.π
  signature: : Y ⟶ cokernel f
  body: coequalizer.π f 0

@[simp]

中文:
缩写 cokernel.π
  签名: : Y ⟶ cokernel f
  定义体: coequalizer.π f 0

@[simp]

Depends on / 依赖: coequalizer
-/
abbrev cokernel.π : Y ⟶ cokernel f :=
  coequalizer.π f 0

@[simp]
/--
theorem `coequalizer_as_cokernel` / 定理 `coequalizer_as_cokernel`

English:
theorem coequalizer_as_cokernel
  statement: coequalizer.π f 0 = cokernel.π f
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 coequalizer_as_cokernel
  结论: coequalizer.π f 0 = cokernel.π f
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `cokernel.condition` / 定理 `cokernel.condition`

English:
theorem cokernel.condition
  statement: f ≫ cokernel.π f = 0
  proof: CokernelCofork.condition _

中文:
定理 cokernel.condition
  结论: f ≫ cokernel.π f = 0
  证明: CokernelCofork.condition _

Depends on / 依赖: CokernelCofork, CokernelCofork.condition, condition
-/
theorem cokernel.condition : f ≫ cokernel.π f = 0 :=
  CokernelCofork.condition _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cokernelIsCokernel` / `cokernelIsCokernel` 的定义

English:
definition cokernelIsCokernel
  signature: :
  body: IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _))

中文:
定义 cokernelIsCokernel
  签名: :
  定义体: IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _))

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
def cokernelIsCokernel :
    IsColimit (Cofork.ofπ (cokernel.π f) ((cokernel.condition f).trans zero_comp.symm)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _))

/--
Definition of `cokernel.desc` / `cokernel.desc` 的定义

English:
abbreviation cokernel.desc
  signature: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  body: (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)

@[reassoc (attr := simp)]

中文:
缩写 cokernel.desc
  签名: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  定义体: (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, cokernelIsCokernel
-/
abbrev cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)

@[reassoc (attr := simp)]
/--
theorem `cokernel.π_desc` / 定理 `cokernel.π_desc`

English:
theorem cokernel.π_desc
  given: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  proof: (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one

中文:
定理 cokernel.π_desc
  条件: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  证明: (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one

Depends on / 依赖: CokernelCofork, CokernelCofork.of, WalkingParallelPair, WalkingParallelPair.one, cokernelIsCokernel
-/
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    cokernel.π f ≫ cokernel.desc f k h = k :=
  (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `colimit_ι_zero_cokernel_desc` / 引理 `colimit_ι_zero_cokernel_desc`

English:
lemma colimit_ι_zero_cokernel_desc
  statement: {C : Type*} [Category* C]
  proof: by
  rw [(colimit.w (parallelPair f 0) WalkingParallelPairHom.left).symm]
  simp

@[simp]

中文:
引理 colimit_ι_zero_cokernel_desc
  结论: {C : 类型} [范畴* C]
  证明: by
  rw [(colimit.w (parallelPair f 0) WalkingParallelPairHom.left).symm]
  simp

@[simp]

Depends on / 依赖: WalkingParallelPairHom, WalkingParallelPairHom.left, colimit, colimit.w, parallelPair
-/
lemma colimit_ι_zero_cokernel_desc {C : Type*} [Category* C]
    [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) [HasCokernel f] :
    colimit.ι (parallelPair f 0) WalkingParallelPair.zero ≫ cokernel.desc f g h = 0 := by
  rw [(colimit.w (parallelPair f 0) WalkingParallelPairHom.left).symm]
  simp

@[simp]
/--
theorem `cokernel.desc_zero` / 定理 `cokernel.desc_zero`

English:
theorem cokernel.desc_zero
  given: {W : C} {h}
  statement: cokernel.desc f (0 : Y ⟶ W) h = 0
  proof: by
  ext; simp

中文:
定理 cokernel.desc_zero
  条件: {W : C} {h}
  结论: cokernel.desc f (0 : Y ⟶ W) h = 0
  证明: by
  ext; simp
-/
theorem cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 := by
  ext; simp

/--
Instance `cokernel.desc_epi` / 实例 `cokernel.desc_epi`

English:
instance cokernel.desc_epi
  signature: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k]
  body: ⟨fun {Z} g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

中文:
实例 cokernel.desc_epi
  签名: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [满态射 k]
  定义体: ⟨fun {Z} g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

Depends on / 依赖: cancel_epi, cokernel, replace
-/
instance cokernel.desc_epi {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k] :
    Epi (cokernel.desc f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

/--
Definition of `cokernel.desc'` / `cokernel.desc'` 的定义

English:
definition cokernel.desc'
  signature: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  body: ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

中文:
定义 cokernel.desc'
  签名: {W : C} (k : Y ⟶ W) (h : f ≫ k = 0)
  定义体: ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

Depends on / 依赖: cokernel, cokernel.desc
-/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    { l : cokernel f ⟶ W // cokernel.π f ≫ l = k } :=
  ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/--
Definition of `cokernel.map` / `cokernel.map` 的定义

English:
abbreviation cokernel.map
  signature: {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
  body: cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])

中文:
缩写 cokernel.map
  签名: {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
  定义体: cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])

Depends on / 依赖: Category, Category.assoc, cokernel, cokernel.desc
-/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])

instance {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [Epi p] [IsIso q] :
    IsIso (cokernel.map _ _ _ _ w) :=
  ⟨cokernel.desc _ (inv q ≫ cokernel.π f) (by simp [← cancel_epi p, ← reassoc_of% w]),
    by cat_disch, by cat_disch⟩

@[simp]
/--
lemma `cokernel.map_id` / 引理 `cokernel.map_id`

English:
lemma cokernel.map_id
  statement: {X Y : C} (f : X ⟶ Y) [HasCokernel f] (q : X ⟶ X)
  proof: by
  cat_disch

中文:
引理 cokernel.map_id
  结论: {X Y : C} (f : X ⟶ Y) [HasCokernel f] (q : X ⟶ X)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma cokernel.map_id {X Y : C} (f : X ⟶ Y) [HasCokernel f] (q : X ⟶ X)
    (w : f ≫ 𝟙 _ = q ≫ f) : cokernel.map f f q (𝟙 _) w = 𝟙 _ := by
  cat_disch

/--
theorem `cokernel.map_desc` / 定理 `cokernel.map_desc`

English:
theorem cokernel.map_desc
  statement: {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
  proof: by
  ext; simp [h₂]

@[simp]

中文:
定理 cokernel.map_desc
  结论: {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
  证明: by
  ext; simp [h₂]

@[simp]
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
    (w : f ≫ g = 0) (f' : X' ⟶ Y') [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X')
    (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by
  ext; simp [h₂]

@[simp]
/--
lemma `cokernel.map_zero` / 引理 `cokernel.map_zero`

English:
lemma cokernel.map_zero
  statement: {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  proof: by
  cat_disch

中文:
引理 cokernel.map_zero
  结论: {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma cokernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCokernel f] [HasCokernel f'] (q : X ⟶ X') (w : f ≫ 0 = q ≫ f') :
    cokernel.map f f' q 0 w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of cokernels. -/
@[simps]
/--
Definition of `cokernel.mapIso` / `cokernel.mapIso` 的定义

English:
definition cokernel.mapIso
  signature: {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
  body: cokernel.map f f' p.hom q.hom w
  inv := cokernel.map f' f p.inv q.inv (by
          refine (cancel_mono q.hom).1 ?_
          simp [w])

中文:
定义 cokernel.mapIso
  签名: {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
  定义体: cokernel.map f f' p.hom q.hom w
  inv := cokernel.map f' f p.inv q.inv (by
          refine (cancel_mono q.hom).1 ?_
          simp [w])

Depends on / 依赖: cokernel, cokernel.map, p.hom, q.hom
-/
def cokernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : cokernel f ≅ cokernel f' where
  hom := cokernel.map f f' p.hom q.hom w
  inv := cokernel.map f' f p.inv q.inv (by
          refine (cancel_mono q.hom).1 ?_
          simp [w])

/--
Instance `cokernel.π_zero_isIso` / 实例 `cokernel.π_zero_isIso`

English:
instance cokernel.π_zero_isIso
  signature: : IsIso (cokernel.π (0 : X ⟶ Y))
  body: coequalizer.π_of_self _

中文:
实例 cokernel.π_zero_isIso
  签名: : 是同构 (cokernel.π (0 : X ⟶ Y))
  定义体: coequalizer.π_of_self _

Depends on / 依赖: coequalizer
-/
instance cokernel.π_zero_isIso : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _

/--
theorem `eq_zero_of_mono_cokernel` / 定理 `eq_zero_of_mono_cokernel`

English:
theorem eq_zero_of_mono_cokernel
  given: [Mono (cokernel.π f)]
  statement: f = 0
  proof: (cancel_mono (cokernel.π f)).1 (by simp)

中文:
定理 eq_zero_of_mono_cokernel
  条件: [单态射 (cokernel.π f)]
  结论: f = 0
  证明: (cancel_mono (cokernel.π f)).1 (by simp)

Depends on / 依赖: cancel_mono, cokernel
-/
theorem eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0 :=
  (cancel_mono (cokernel.π f)).1 (by simp)

/--
Definition of `cokernelZeroIsoTarget` / `cokernelZeroIsoTarget` 的定义

English:
definition cokernelZeroIsoTarget
  signature: : cokernel (0 : X ⟶ Y) ≅ Y
  body: coequalizer.isoTargetOfSelf 0

中文:
定义 cokernelZeroIsoTarget
  签名: : cokernel (0 : X ⟶ Y) ≅ Y
  定义体: coequalizer.isoTargetOfSelf 0

Depends on / 依赖: coequalizer, coequalizer.isoTargetOfSelf, isoTargetOfSelf
-/
def cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y :=
  coequalizer.isoTargetOfSelf 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cokernelZeroIsoTarget_hom` / 定理 `cokernelZeroIsoTarget_hom`

English:
theorem cokernelZeroIsoTarget_hom
  proof: by
  ext; simp [cokernelZeroIsoTarget]

@[simp]

中文:
定理 cokernelZeroIsoTarget_hom
  证明: by
  ext; simp [cokernelZeroIsoTarget]

@[simp]

Depends on / 依赖: cokernelZeroIsoTarget
-/
theorem cokernelZeroIsoTarget_hom :
    cokernelZeroIsoTarget.hom = cokernel.desc (0 : X ⟶ Y) (𝟙 Y) (by simp) := by
  ext; simp [cokernelZeroIsoTarget]

@[simp]
/--
theorem `cokernelZeroIsoTarget_inv` / 定理 `cokernelZeroIsoTarget_inv`

English:
theorem cokernelZeroIsoTarget_inv
  statement: cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y)
  proof: rfl

中文:
定理 cokernelZeroIsoTarget_inv
  结论: cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y)
  证明: rfl
-/
theorem cokernelZeroIsoTarget_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y) :=
  rfl

/--
Definition of `cokernelIsoOfEq` / `cokernelIsoOfEq` 的定义

English:
definition cokernelIsoOfEq
  signature: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  body: HasColimit.isoOfNatIso (by simp [h]; rfl)

中文:
定义 cokernelIsoOfEq
  签名: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  定义体: HasColimit.isoOfNatIso (by simp [h]; rfl)

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, isoOfNatIso
-/
def cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel f ≅ cokernel g :=
  HasColimit.isoOfNatIso (by simp [h]; rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cokernelIsoOfEq_refl` / 定理 `cokernelIsoOfEq_refl`

English:
theorem cokernelIsoOfEq_refl
  given: {h : f = f}
  statement: cokernelIsoOfEq h = Iso.refl (cokernel f)
  proof: by
  ext; simp [cokernelIsoOfEq]

@[reassoc (attr := simp)]

中文:
定理 cokernelIsoOfEq_refl
  条件: {h : f = f}
  结论: cokernelIsoOfEq h = 同构.refl (cokernel f)
  证明: by
  ext; simp [cokernelIsoOfEq]

@[reassoc (attr := simp)]

Depends on / 依赖: cokernelIsoOfEq
-/
theorem cokernelIsoOfEq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel f) := by
  ext; simp [cokernelIsoOfEq]

@[reassoc (attr := simp)]
/--
theorem `π_comp_cokernelIsoOfEq_hom` / 定理 `π_comp_cokernelIsoOfEq_hom`

English:
theorem π_comp_cokernelIsoOfEq_hom
  given: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  proof: by
  cases h; simp

@[reassoc (attr := simp)]

中文:
定理 π_comp_cokernelIsoOfEq_hom
  条件: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  证明: by
  cases h; simp

@[reassoc (attr := simp)]
-/
theorem π_comp_cokernelIsoOfEq_hom {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π f ≫ (cokernelIsoOfEq h).hom = cokernel.π g := by
  cases h; simp

@[reassoc (attr := simp)]
/--
theorem `π_comp_cokernelIsoOfEq_inv` / 定理 `π_comp_cokernelIsoOfEq_inv`

English:
theorem π_comp_cokernelIsoOfEq_inv
  given: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  proof: by
  cases h; simp

@[reassoc (attr := simp)]

中文:
定理 π_comp_cokernelIsoOfEq_inv
  条件: {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  证明: by
  cases h; simp

@[reassoc (attr := simp)]
-/
theorem π_comp_cokernelIsoOfEq_inv {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).inv = cokernel.π _ := by
  cases h; simp

@[reassoc (attr := simp)]
/--
theorem `cokernelIsoOfEq_hom_comp_desc` / 定理 `cokernelIsoOfEq_hom_comp_desc`

English:
theorem cokernelIsoOfEq_hom_comp_desc
  statement: {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  proof: by
  cases h; simp

@[reassoc (attr := simp)]

中文:
定理 cokernelIsoOfEq_hom_comp_desc
  结论: {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  证明: by
  cases h; simp

@[reassoc (attr := simp)]
-/
theorem cokernelIsoOfEq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).hom ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [h, he]) := by
  cases h; simp

@[reassoc (attr := simp)]
/--
theorem `cokernelIsoOfEq_inv_comp_desc` / 定理 `cokernelIsoOfEq_inv_comp_desc`

English:
theorem cokernelIsoOfEq_inv_comp_desc
  statement: {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  proof: by
  cases h; simp

@[simp]

中文:
定理 cokernelIsoOfEq_inv_comp_desc
  结论: {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
  证明: by
  cases h; simp

@[simp]
-/
theorem cokernelIsoOfEq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [← h, he]) := by
  cases h; simp

@[simp]
/--
theorem `cokernelIsoOfEq_trans` / 定理 `cokernelIsoOfEq_trans`

English:
theorem cokernelIsoOfEq_trans
  statement: {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
  proof: by
  cases w₁; simp

中文:
定理 cokernelIsoOfEq_trans
  结论: {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
  证明: by
  cases w₁; simp
-/
theorem cokernelIsoOfEq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
    (w₁ : f = g) (w₂ : g = h) :
    cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂ = cokernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}

/--
theorem `cokernel_not_mono_of_nonzero` / 定理 `cokernel_not_mono_of_nonzero`

English:
theorem cokernel_not_mono_of_nonzero
  given: (w : f != 0)
  statement: ¬Mono (cokernel.π f)
  proof: fun _ =>
  w (eq_zero_of_mono_cokernel f)

中文:
定理 cokernel_not_mono_of_nonzero
  条件: (w : f != 0)
  结论: ¬单态射 (cokernel.π f)
  证明: fun _ =>
  w (eq_zero_of_mono_cokernel f)
-/
theorem cokernel_not_mono_of_nonzero (w : f != 0) : ¬Mono (cokernel.π f) := fun _ =>
  w (eq_zero_of_mono_cokernel f)

/--
theorem `cokernel_not_iso_of_nonzero` / 定理 `cokernel_not_iso_of_nonzero`

English:
theorem cokernel_not_iso_of_nonzero
  given: (w : f != 0)
  statement: IsIso (cokernel.π f) -> False
  proof: fun _ =>
  cokernel_not_mono_of_nonzero w inferInstance

中文:
定理 cokernel_not_iso_of_nonzero
  条件: (w : f != 0)
  结论: 是同构 (cokernel.π f) -> 假
  证明: fun _ =>
  cokernel_not_mono_of_nonzero w inferInstance
-/
theorem cokernel_not_iso_of_nonzero (w : f != 0) : IsIso (cokernel.π f) -> False := fun _ =>
  cokernel_not_mono_of_nonzero w inferInstance

set_option backward.defeqAttrib.useBackward true in
-- TODO the remainder of this section has obvious generalizations to `HasCoequalizer f g`.
/--
Instance `hasCokernel_comp_iso` / 实例 `hasCokernel_comp_iso`

English:
instance hasCokernel_comp_iso
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g]
  body: ⟨{ cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        isColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← Category.assoc, CokernelCofork.condition]))
            (by simp) fun s (m : cokernel _ ⟶ _) w => by
            simp_rw [← w]
            apply coequalizer.hom_ext
            simp }⟩

中文:
实例 hasCokernel_comp_iso
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [是同构 g]
  定义体: ⟨{ cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        isColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← Category.assoc, CokernelCofork.condition]))
            (by simp) fun s (m : cokernel _ ⟶ _) w => by
            simp_rw [← w]
            apply coequalizer.hom_ext
            simp }⟩

Depends on / 依赖: Category, Category.assoc, CokernelCofork, CokernelCofork.condition, CokernelCofork.of, cocone, coequalizer, coequalizer.hom_ext, cokernel, cokernel.desc, condition, hom_ext, isColimit, isColimitAux, simp_rw
-/
instance hasCokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    HasCokernel (f ≫ g) where
  exists_colimit :=
    ⟨{ cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        isColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← Category.assoc, CokernelCofork.condition]))
            (by simp) fun s (m : cokernel _ ⟶ _) w => by
            simp_rw [← w]
            apply coequalizer.hom_ext
            simp }⟩

/-- When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
/--
Definition of `cokernelCompIsIso` / `cokernelCompIsIso` 的定义

English:
definition cokernelCompIsIso
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g]
  body: cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition])

中文:
定义 cokernelCompIsIso
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [是同构 g]
  定义体: cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition])

Depends on / 依赖: cokernel, cokernel.desc
-/
def cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    cokernel (f ≫ g) ≅ cokernel f where
  hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition])

/--
Instance `hasCokernel_epi_comp` / 实例 `hasCokernel_epi_comp`

English:
instance hasCokernel_epi_comp
  signature: {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [Epi g]
  body: ⟨⟨{ cocone := _
        isColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩

中文:
实例 hasCokernel_epi_comp
  签名: {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [满态射 g]
  定义体: ⟨⟨{ cocone := _
        isColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩

Depends on / 依赖: cocone, colimit, colimit.isColimit, isCokernelEpiComp, isColimit
-/
instance hasCokernel_epi_comp {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [Epi g] :
    HasCokernel (g ≫ f) :=
  ⟨⟨{ cocone := _
        isColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩

/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
/--
Definition of `cokernelEpiComp` / `cokernelEpiComp` 的定义

English:
definition cokernelEpiComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g]
  body: cokernel.desc _ (cokernel.π g) (by simp)
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f]; rw [← Category.assoc]
        simp)

@[deprecated (since := "2026-07-03")] alias cokernel.congr := cokernelIsoOfEq

中文:
定义 cokernelEpiComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [满态射 f] [HasCokernel g]
  定义体: cokernel.desc _ (cokernel.π g) (by simp)
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f]; rw [← Category.assoc]
        simp)

@[deprecated (since := "2026-07-03")] alias cokernel.congr := cokernelIsoOfEq

Depends on / 依赖: cokernel, cokernel.desc
-/
def cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g] :
    cokernel (f ≫ g) ≅ cokernel g where
  hom := cokernel.desc _ (cokernel.π g) (by simp)
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f]; rw [← Category.assoc]
        simp)

@[deprecated (since := "2026-07-03")] alias cokernel.congr := cokernelIsoOfEq

/--
lemma `isZero_cokernel_of_epi` / 引理 `isZero_cokernel_of_epi`

English:
lemma isZero_cokernel_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f]
  proof: CokernelCofork.IsColimit.isZero_of_epi (c := CokernelCofork.ofπ _ (cokernel.condition f))
    (cokernelIsCokernel f)

中文:
引理 isZero_cokernel_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f] [HasCokernel f]
  证明: CokernelCofork.IsColimit.isZero_of_epi (c := CokernelCofork.ofπ _ (cokernel.condition f))
    (cokernelIsCokernel f)

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.isZero_of_epi, CokernelCofork.of, IsColimit, cokernel, cokernel.condition, cokernelIsCokernel, condition, isZero_of_epi
-/
lemma isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] :
    IsZero (cokernel f) :=
  CokernelCofork.IsColimit.isZero_of_epi (c := CokernelCofork.ofπ _ (cokernel.condition f))
    (cokernelIsCokernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
@[simps! pt]
/--
Definition of `cokernel.zeroCokernelCofork` / `cokernel.zeroCokernelCofork` 的定义

English:
definition cokernel.zeroCokernelCofork
  signature: : CokernelCofork f
  body: CokernelCofork.ofπ (0 : Y ⟶ 0) comp_zero

@[simp]

中文:
定义 cokernel.zeroCokernelCofork
  签名: : 余核余叉 f
  定义体: CokernelCofork.ofπ (0 : Y ⟶ 0) comp_zero

@[simp]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, comp_zero
-/
def cokernel.zeroCokernelCofork : CokernelCofork f :=
    CokernelCofork.ofπ (0 : Y ⟶ 0) comp_zero

@[simp]
/--
lemma `cokernel.zeroCokernelCofork_π` / 引理 `cokernel.zeroCokernelCofork_π`

English:
lemma cokernel.zeroCokernelCofork_π
  statement: (cokernel.zeroCokernelCofork f).π = 0
  proof: rfl

中文:
引理 cokernel.zeroCokernelCofork_π
  结论: (cokernel.zeroCokernelCofork f).π = 0
  证明: rfl
-/
lemma cokernel.zeroCokernelCofork_π : (cokernel.zeroCokernelCofork f).π = 0 := rfl

/--
Definition of `cokernel.isColimitCoconeZeroCocone` / `cokernel.isColimitCoconeZeroCocone` 的定义

English:
definition cokernel.isColimitCoconeZeroCocone
  signature: [Epi f]
  body: Cofork.IsColimit.mk _ (fun _ => 0)
    fun _ => by simp [zero_of_epi_comp f _]
    fun _ _ _ => zero_of_from_zero _

中文:
定义 cokernel.isColimitCoconeZeroCocone
  签名: [满态射 f]
  定义体: Cofork.IsColimit.mk _ (fun _ => 0)
    fun _ => by simp [zero_of_epi_comp f _]
    fun _ _ _ => zero_of_from_zero _

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, zero_of_epi_comp, zero_of_from_zero
-/
def cokernel.isColimitCoconeZeroCocone [Epi f] : IsColimit (cokernel.zeroCokernelCofork f) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    fun _ => by simp [zero_of_epi_comp f _]
    fun _ _ _ => zero_of_from_zero _

/--
Definition of `cokernel.ofEpi` / `cokernel.ofEpi` 的定义

English:
definition cokernel.ofEpi
  signature: [HasCokernel f] [Epi f]
  body: Functor.mapIso (Cocone.forget _)
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)

中文:
定义 cokernel.ofEpi
  签名: [HasCokernel f] [满态射 f]
  定义体: Functor.mapIso (Cocone.forget _)
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)

Depends on / 依赖: Cocone, Cocone.forget, Functor, Functor.mapIso, IsColimit, IsColimit.uniqueUpToIso, cokernel, cokernel.isColimitCoconeZeroCocone, colimit, colimit.isColimit, forget, isColimit, isColimitCoconeZeroCocone, mapIso, parallelPair, uniqueUpToIso
-/
def cokernel.ofEpi [HasCokernel f] [Epi f] : cokernel f ≅ 0 :=
Functor.mapIso (Cocone.forget _)
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)

/--
theorem `cokernel.π_of_epi` / 定理 `cokernel.π_of_epi`

English:
theorem cokernel.π_of_epi
  given: [HasCokernel f] [Epi f]
  statement: cokernel.π f = 0
  proof: zero_of_target_iso_zero _ (cokernel.ofEpi f)

中文:
定理 cokernel.π_of_epi
  条件: [HasCokernel f] [满态射 f]
  结论: cokernel.π f = 0
  证明: zero_of_target_iso_zero _ (cokernel.ofEpi f)

Depends on / 依赖: cokernel, cokernel.ofEpi, zero_of_target_iso_zero
-/
theorem cokernel.π_of_epi [HasCokernel f] [Epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero _ (cokernel.ofEpi f)

end HasZeroObject

section MonoFactorisation

variable {f}

@[simp]
/--
theorem `MonoFactorisation.kernel_ι_comp` / 定理 `MonoFactorisation.kernel_ι_comp`

English:
theorem MonoFactorisation.kernel_ι_comp
  given: [HasKernel f] (F : MonoFactorisation f)
  proof: by
  rw [← cancel_mono F.m]; rw [zero_comp]; rw [Category.assoc]; rw [F.fac]; rw [kernel.condition]

中文:
定理 单态射分解.kernel_ι_comp
  条件: [HasKernel f] (F : 单态射分解 f)
  证明: by
  rw [← cancel_mono F.m]; rw [zero_comp]; rw [Category.assoc]; rw [F.fac]; rw [kernel.condition]

Depends on / 依赖: Category, Category.assoc, F.fac, cancel_mono, condition, kernel, kernel.condition, zero_comp
-/
theorem MonoFactorisation.kernel_ι_comp [HasKernel f] (F : MonoFactorisation f) :
    kernel.ι f ≫ F.e = 0 := by
  rw [← cancel_mono F.m]; rw [zero_comp]; rw [Category.assoc]; rw [F.fac]; rw [kernel.condition]

end MonoFactorisation

section HasImage

/-- The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
/--
Definition of `cokernelImageι` / `cokernelImageι` 的定义

English:
definition cokernelImageι
  signature: {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
  body: cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← HasZeroMorphisms.comp_zero (Limits.factorThruImage f)]; rw [Category.assoc]; rw [cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [Category.assoc]; rw [cokernel.condition]; rw [HasZeroMorphisms.comp_zero])

中文:
定义 cokernelImageι
  签名: {X Y : C} (f : X ⟶ Y) [有像 f] [HasCokernel (像.ι f)] [HasCokernel f]
  定义体: cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← HasZeroMorphisms.comp_zero (Limits.factorThruImage f)]; rw [Category.assoc]; rw [cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [Category.assoc]; rw [cokernel.condition]; rw [HasZeroMorphisms.comp_zero])

Depends on / 依赖: Category, Category.assoc, HasZeroMorphisms, HasZeroMorphisms.comp_zero, Limits, Limits.factorThruImage, cancel_epi, cokernel, cokernel.condition, cokernel.desc, comp_zero, condition, factorThruImage, image.fac
-/
def cokernelImageι {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
    [Epi (factorThruImage f)] : cokernel (image.ι f) ≅ cokernel f where
  hom :=
    cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← HasZeroMorphisms.comp_zero (Limits.factorThruImage f)]; rw [Category.assoc]; rw [cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [Category.assoc]; rw [cokernel.condition]; rw [HasZeroMorphisms.comp_zero])

section

variable (f : X ⟶ Y) [HasKernel f] [HasImage f] [HasKernel (factorThruImage f)]

/--
Definition of `kernelFactorThruImage` / `kernelFactorThruImage` 的定义

English:
definition kernelFactorThruImage
  signature: : kernel (factorThruImage f) ≅ kernel f
  body: (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernelIsoOfEq (by simp))

@[reassoc (attr := simp)]

中文:
定义 kernelFactorThruImage
  签名: : kernel (factorThruImage f) ≅ kernel f
  定义体: (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernelIsoOfEq (by simp))

@[reassoc (attr := simp)]

Depends on / 依赖: factorThruImage, kernelCompMono, kernelIsoOfEq
-/
def kernelFactorThruImage : kernel (factorThruImage f) ≅ kernel f :=
  (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernelIsoOfEq (by simp))

@[reassoc (attr := simp)]
/--
theorem `kernelFactorThruImage_hom_comp_ι` / 定理 `kernelFactorThruImage_hom_comp_ι`

English:
theorem kernelFactorThruImage_hom_comp_ι
  proof: by
  simp [kernelFactorThruImage]

@[reassoc (attr := simp)]

中文:
定理 kernelFactorThruImage_hom_comp_ι
  证明: by
  simp [kernelFactorThruImage]

@[reassoc (attr := simp)]

Depends on / 依赖: kernelFactorThruImage
-/
theorem kernelFactorThruImage_hom_comp_ι :
    (kernelFactorThruImage f).hom ≫ kernel.ι f = kernel.ι (factorThruImage f) := by
  simp [kernelFactorThruImage]

@[reassoc (attr := simp)]
/--
theorem `kernelFactorThruImage_inv_comp_ι` / 定理 `kernelFactorThruImage_inv_comp_ι`

English:
theorem kernelFactorThruImage_inv_comp_ι
  proof: by
  simp [kernelFactorThruImage]

中文:
定理 kernelFactorThruImage_inv_comp_ι
  证明: by
  simp [kernelFactorThruImage]

Depends on / 依赖: kernelFactorThruImage
-/
theorem kernelFactorThruImage_inv_comp_ι :
    (kernelFactorThruImage f).inv ≫ kernel.ι (factorThruImage f) = kernel.ι f := by
  simp [kernelFactorThruImage]

end

end HasImage

section

/--
theorem `cokernel.π_of_zero` / 定理 `cokernel.π_of_zero`

English:
theorem cokernel.π_of_zero
  given: {f : X ⟶ Y} [HasCokernel f] (eq : f = 0)
  proof: coequalizer.π_of_eq eq

中文:
定理 cokernel.π_of_zero
  条件: {f : X ⟶ Y} [HasCokernel f] (eq : f = 0)
  证明: coequalizer.π_of_eq eq

Depends on / 依赖: coequalizer
-/
theorem cokernel.π_of_zero {f : X ⟶ Y} [HasCokernel f] (eq : f = 0) :
    IsIso (cokernel.π f) := coequalizer.π_of_eq eq

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/--
Instance `kernel.of_cokernel_of_epi` / 实例 `kernel.of_cokernel_of_epi`

English:
instance kernel.of_cokernel_of_epi
  signature: [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f]
  body: equalizer.ι_of_eq cokernel.π_of_epi f

中文:
实例 kernel.of_cokernel_of_epi
  签名: [HasCokernel f] [HasKernel (cokernel.π f)] [满态射 f]
  定义体: equalizer.ι_of_eq cokernel.π_of_epi f

Depends on / 依赖: cokernel, equalizer
-/
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
equalizer.ι_of_eq cokernel.π_of_epi f

/--
Instance `cokernel.of_kernel_of_mono` / 实例 `cokernel.of_kernel_of_mono`

English:
instance cokernel.of_kernel_of_mono
  signature: [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f]
  body: coequalizer.π_of_eq kernel.ι_of_mono f

中文:
实例 cokernel.of_kernel_of_mono
  签名: [HasKernel f] [HasCokernel (kernel.ι f)] [单态射 f]
  定义体: coequalizer.π_of_eq kernel.ι_of_mono f

Depends on / 依赖: coequalizer, kernel
-/
instance cokernel.of_kernel_of_mono [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f] :
    IsIso (cokernel.π (kernel.ι f)) :=
coequalizer.π_of_eq kernel.ι_of_mono f

/--
Definition of `zeroCokernelOfZeroCancel` / `zeroCokernelOfZeroCancel` 的定义

English:
definition zeroCokernelOfZeroCancel
  signature: {X Y : C} (f : X ⟶ Y)
  body: Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

中文:
定义 zeroCokernelOfZeroCancel
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.condition, HasZeroObject, HasZeroObject.from_zero_ext, IsColimit, comp_zero, condition, from_zero_ext
-/
def zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y)
    (hf : forall (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) :
    IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show f ≫ 0 = 0 by simp)) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsCokernel.ofIsoComp` / `IsCokernel.ofIsoComp` 的定义

English:
definition IsCokernel.ofIsoComp
  signature: {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) {s : CokernelCofork f}
  body: Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Cofork.IsColimit.hom_ext hs
      simpa using h

中文:
定义 IsCokernel.ofIsoComp
  签名: {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) {s : 余核余叉 f}
  定义体: Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Cofork.IsColimit.hom_ext hs
      simpa using h

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.of, IsColimit, hom_ext, hs.desc
-/
def IsCokernel.ofIsoComp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) {s : CokernelCofork f}
    (hs : IsColimit s) :
    IsColimit
      (CokernelCofork.ofπ (Cofork.π s) <| show l ≫ Cofork.π s = 0 by simp [i.eq_inv_comp.2 h]) :=
  Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Cofork.IsColimit.hom_ext hs
      simpa using h

/--
Definition of `cokernel.ofIsoComp` / `cokernel.ofIsoComp` 的定义

English:
definition cokernel.ofIsoComp
  signature: [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f)
  body: IsCokernel.ofIsoComp f l i h colimit.isColimit _

中文:
定义 cokernel.ofIsoComp
  签名: [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f)
  定义体: IsCokernel.ofIsoComp f l i h colimit.isColimit _

Depends on / 依赖: IsCokernel, IsCokernel.ofIsoComp, colimit, colimit.isColimit, isColimit, ofIsoComp
-/
def cokernel.ofIsoComp [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
    IsColimit
      (CokernelCofork.ofπ (cokernel.π f) <|
        show l ≫ cokernel.π f = 0 by simp [i.eq_inv_comp.2 h]) :=
IsCokernel.ofIsoComp f l i h colimit.isColimit _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsCokernel.cokernelIso` / `IsCokernel.cokernelIso` 的定义

English:
definition IsCokernel.cokernelIso
  signature: {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s)
  body: IsColimit.ofIsoColimit hs
    Cocone.ext i fun j => by
      cases j
      · dsimp; rw [← h]; simp
      · exact h

中文:
定义 IsCokernel.cokernelIso
  签名: {Z : C} (l : Y ⟶ Z) {s : 余核余叉 f} (hs : 是余极限 s)
  定义体: IsColimit.ofIsoColimit hs
    Cocone.ext i fun j => by
      cases j
      · dsimp; rw [← h]; simp
      · exact h

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, ofIsoColimit
-/
def IsCokernel.cokernelIso {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s)
    (i : s.pt ≅ Z) (h : Cofork.π s ≫ i.hom = l) :
    IsColimit (CokernelCofork.ofπ l <| show f ≫ l = 0 by simp [← h]) :=
IsColimit.ofIsoColimit hs
    Cocone.ext i fun j => by
      cases j
      · dsimp; rw [← h]; simp
      · exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsCokernel.ofIso` / `IsCokernel.ofIso` 的定义

English:
definition IsCokernel.ofIso
  signature: {X' Y' : C} {f' : X' ⟶ Y'} {s : CokernelCofork f} (hs : IsColimit s)
  body: let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α.symm s).symm hs)
    Cocone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

中文:
定义 IsCokernel.ofIso
  签名: {X' Y' : C} {f' : X' ⟶ Y'} {s : 余核余叉 f} (hs : 是余极限 s)
  定义体: let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α.symm s).symm hs)
    Cocone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

Depends on / 依赖: Cocone, Cocone.ext, H.symm, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, ofIsoColimit, parallelPair, parallelPairIsoMk, precomposeHomEquiv
-/
def IsCokernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : CokernelCofork f} (hs : IsColimit s)
    (s' : CokernelCofork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : eY.hom ≫ s'.π = s.π ≫ e.hom) :
    IsColimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α.symm s).symm hs)
    Cocone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

/--
Definition of `cokernel.cokernelIso` / `cokernel.cokernelIso` 的定义

English:
definition cokernel.cokernelIso
  signature: [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
  body: IsCokernel.cokernelIso f l (colimit.isColimit _) i h

中文:
定义 cokernel.cokernelIso
  签名: [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
  定义体: IsCokernel.cokernelIso f l (colimit.isColimit _) i h

Depends on / 依赖: IsCokernel, IsCokernel.cokernelIso, cokernelIso, colimit, colimit.isColimit, isColimit
-/
def cokernel.cokernelIso [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
    (h : cokernel.π f ≫ i.hom = l) :
    IsColimit (@CokernelCofork.ofπ _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsCokernel.cokernelIso f l (colimit.isColimit _) i h

end Transport

section Comparison

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

/--
Definition of `kernelComparison` / `kernelComparison` 的定义

English:
definition kernelComparison
  signature: [HasKernel f] [HasKernel (G.map f)]
  body: kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]

中文:
定义 kernelComparison
  签名: [HasKernel f] [HasKernel (G.map f)]
  定义体: kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_zero, G.map, G.map_comp, condition, kernel, kernel.condition, kernel.lift, map_comp, map_zero
-/
def kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ kernel (G.map f) :=
  kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
/--
theorem `kernelComparison_comp_ι` / 定理 `kernelComparison_comp_ι`

English:
theorem kernelComparison_comp_ι
  given: [HasKernel f] [HasKernel (G.map f)]
  proof: kernel.lift_ι _ _ _

@[reassoc (attr := simp)]

中文:
定理 kernelComparison_comp_ι
  条件: [HasKernel f] [HasKernel (G.map f)]
  证明: kernel.lift_ι _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: kernel, kernel.lift_, uncurry
-/
theorem kernelComparison_comp_ι [HasKernel f] [HasKernel (G.map f)] :
    kernelComparison f G ≫ kernel.ι (G.map f) = G.map (kernel.ι f) :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
/--
theorem `map_lift_kernelComparison` / 定理 `map_lift_kernelComparison`

English:
theorem map_lift_kernelComparison
  statement: [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
  proof: by
  ext; simp [← G.map_comp]

@[reassoc]

中文:
定理 map_lift_kernelComparison
  结论: [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
  证明: by
  ext; simp [← G.map_comp]

@[reassoc]

Depends on / 依赖: G.map_comp, map_comp, uncurry
-/
theorem map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
    (w : h ≫ f = 0) :
    G.map (kernel.lift _ h w) ≫ kernelComparison f G =
      kernel.lift _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
/--
theorem `kernelComparison_comp_kernel_map` / 定理 `kernelComparison_comp_kernel_map`

English:
theorem kernelComparison_comp_kernel_map
  statement: {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
  proof: kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

中文:
定理 kernelComparison_comp_kernel_map
  结论: {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
  证明: kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

Depends on / 依赖: G.congr_map, G.map_comp, G.map_zero, condition, congr_map, kernel, kernel.condition, kernel.lift_, kernel.lift_map, lift_map, map_comp, map_zero
-/
theorem kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
    (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernelComparison f G ≫
        kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (kernel.map f g p q hpq) ≫ kernelComparison g G :=
  kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

/--
Definition of `cokernelComparison` / `cokernelComparison` 的定义

English:
definition cokernelComparison
  signature: [HasCokernel f] [HasCokernel (G.map f)]
  body: cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]

中文:
定义 cokernelComparison
  签名: [HasCokernel f] [HasCokernel (G.map f)]
  定义体: cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_zero, G.map, G.map_comp, coequalizer, cokernel, cokernel.condition, cokernel.desc, condition, curryHomEquiv, injective, map_comp, map_zero
-/
def cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel (G.map f) ⟶ G.obj (cokernel f) :=
  cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
/--
theorem `π_comp_cokernelComparison` / 定理 `π_comp_cokernelComparison`

English:
theorem π_comp_cokernelComparison
  given: [HasCokernel f] [HasCokernel (G.map f)]
  proof: cokernel.π_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 π_comp_cokernelComparison
  条件: [HasCokernel f] [HasCokernel (G.map f)]
  证明: cokernel.π_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: cokernel, curryHomEquiv, injective, symm.injective
-/
theorem π_comp_cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel.π (G.map f) ≫ cokernelComparison f G = G.map (cokernel.π _) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
/--
theorem `cokernelComparison_map_desc` / 定理 `cokernelComparison_map_desc`

English:
theorem cokernelComparison_map_desc
  statement: [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
  proof: by
  ext; simp [← G.map_comp]

@[reassoc]

中文:
定理 cokernelComparison_map_desc
  结论: [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
  证明: by
  ext; simp [← G.map_comp]

@[reassoc]

Depends on / 依赖: Category, Category.comp_id, G.map_comp, comp_id, map_comp
-/
theorem cokernelComparison_map_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
    (w : f ≫ h = 0) :
    cokernelComparison f G ≫ G.map (cokernel.desc _ h w) =
      cokernel.desc _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
/--
theorem `cokernel_map_comp_cokernelComparison` / 定理 `cokernel_map_comp_cokernelComparison`

English:
theorem cokernel_map_comp_cokernelComparison
  statement: {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
  proof: cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (cokernel.π_desc _ _ _))

中文:
定理 cokernel_map_comp_cokernelComparison
  结论: {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
  证明: cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (cokernel.π_desc _ _ _))

Depends on / 依赖: G.congr_map, G.map_comp, G.map_zero, cokernel, cokernel.condition, cokernel.map_desc, condition, congr_map, map_comp, map_desc, map_zero
-/
theorem cokernel_map_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
    (g : X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    cokernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        cokernelComparison _ G =
      cokernelComparison _ G ≫ G.map (cokernel.map f g p q hpq) :=
  cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (cokernel.π_desc _ _ _))

end Comparison

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C]

/--
Definition of `HasKernels` / `HasKernels` 的定义

English:
class HasKernels
  parameters: : Prop where
  axioms and operations (1):
    - has_limit : forall {X Y : C} (f : X ⟶ Y), HasKernel f  [default: by infer_instance]

中文:
类 有Kernels
  参数: : 命题 where
  公理与运算 (1 个):
    - has_limit : 对任意 {X Y : C} (f : X ⟶ Y), HasKernel f  [默认: by infer_instance]

Depends on / 依赖: Iso.inv_hom_id_assoc, _ihom_ev_app, associator_inv_naturality_middle_assoc, cancel_epi, compTranspose_eq, comp_eq, comp_whiskerRight_assoc, curry_natural_left, fun_, infer_instance, inv_hom_id_assoc, triangle_assoc_comp_right_assoc, uncurry_curry, uncurry_injective, uncurry_pre, whiskerLeft_curry, whiskerLeft_inv_hom_assoc
-/
class HasKernels : Prop where
  has_limit : forall {X Y : C} (f : X ⟶ Y), HasKernel f := by infer_instance

/--
Definition of `HasCokernels` / `HasCokernels` 的定义

English:
class HasCokernels
  parameters: : Prop where
  axioms and operations (1):
    - has_colimit : forall {X Y : C} (f : X ⟶ Y), HasCokernel f  [default: by infer_instance]

中文:
类 有余kernels
  参数: : 命题 where
  公理与运算 (1 个):
    - has_colimit : 对任意 {X Y : C} (f : X ⟶ Y), HasCokernel f  [默认: by infer_instance]

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_ho, Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerRight_id_assoc, _ihom_ev_app, associator_inv_naturality_right_assoc, cancel_epi, compTranspose_eq, comp_eq, curry_natural_left, hom_inv_id_assoc, infer_instance, inv_ho, inv_hom_id_assoc, uncurry_curry, uncurry_ihom_map, uncurry_injective
-/
class HasCokernels : Prop where
  has_colimit : forall {X Y : C} (f : X ⟶ Y), HasCokernel f := by infer_instance

attribute [instance 100] HasKernels.has_limit HasCokernels.has_colimit

instance (priority := 100) hasKernels_of_hasEqualizers [HasEqualizers C] : HasKernels C where

instance (priority := 100) hasCokernels_of_hasCoequalizers [HasCoequalizers C] :
    HasCokernels C where

section HasKernels
variable [HasKernels C]

/-- The kernel of an arrow is natural. -/
@[simps]
/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : Arrow C ⥤ C where
  body: kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

中文:
定义 ker
  签名: : 箭头 C ⥤ C where
  定义体: kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

Depends on / 依赖: Category, Category.assoc, curry_natural_right, f.hom, kernel
-/
noncomputable def ker : Arrow C ⥤ C where
  obj f := kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ker.ι` / `ker.ι` 的定义

English:
definition ker.ι
  signature: : ker (C := C) ⟶ Arrow.leftFunc where app f
  body: kernel.ι _

中文:
定义 ker.ι
  签名: : ker (C := C) ⟶ 箭头.leftFunc where app f
  定义体: kernel.ι _

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerRight_id, _comp, _ihom_map, inv_hom_id_assoc, tensorHom_def_assoc, unitors_equal, whiskerLeft_curry, whiskerRight_id
-/
@[simps] def ker.ι : ker (C := C) ⟶ Arrow.leftFunc where app f := kernel.ι _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `ker.condition` / 引理 `ker.condition`

English:
lemma ker.condition
  statement: ι C ≫ Arrow.leftToRight = 0
  proof: by cat_disch

中文:
引理 ker.condition
  结论: ι C ≫ 箭头.leftToRight = 0
  证明: by cat_disch

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, Functor, Functor.isLeftAdjoint_of_iso, isLeftAdjoint_of_iso, tensorLeftIsoTensorRight
-/
@[reassoc (attr := simp)] lemma ker.condition : ι C ≫ Arrow.leftToRight = 0 := by cat_disch

end HasKernels

section HasCokernels
variable [HasCokernels C]

/-- The cokernel of an arrow is natural. -/
@[simps]
/--
Definition of `coker` / `coker` 的定义

English:
definition coker
  signature: : Arrow C ⥤ C where
  body: cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

中文:
定义 coker
  签名: : 箭头 C ⥤ C where
  定义体: cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

Depends on / 依赖: MonoidalClosed, MonoidalClosed.internalHomAdjunction, cokernel, f.hom, preservesLimitsOfShape_flip_obj
-/
noncomputable def coker : Arrow C ⥤ C where
  obj f := cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `coker.π` / `coker.π` 的定义

English:
definition coker.π
  signature: : Arrow.rightFunc ⟶ coker (C := C) where app f
  body: cokernel.π _

中文:
定义 coker.π
  签名: : 箭头.rightFunc ⟶ coker (C := C) where app f
  定义体: cokernel.π _
-/
@[simps] def coker.π : Arrow.rightFunc ⟶ coker (C := C) where app f := cokernel.π _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `coker.condition` / 引理 `coker.condition`

English:
lemma coker.condition
  statement: Arrow.leftToRight ≫ π C = 0
  proof: by cat_disch

中文:
引理 coker.condition
  结论: 箭头.leftToRight ≫ π C = 0
  证明: by cat_disch
-/
@[reassoc (attr := simp)] lemma coker.condition : Arrow.leftToRight ≫ π C = 0 := by cat_disch

end HasCokernels

end CategoryTheory.Limits
