/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Normal mono categories with finite products and kernels have all equalizers.

This, and the dual result, are used in the development of abelian categories.
-/

public section


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace CategoryTheory.NormalMonoCategory

variable [HasFiniteProducts C] [HasKernels C] [IsNormalMonoCategory C]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullback_of_mono` / 引理 `pullback_of_mono`

English:
lemma pullback_of_mono
  given: {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b]
  proof: let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g))
      calc kernel.ι (prod.lift f g) ≫ f
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.fst := by rw [prod.lift_fst]
      

中文:
引理 pullback_of_mono
  条件: {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b]
  证明: let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g))
      calc kernel.ι (prod.lift f g) ≫ f
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.fst := by rw [prod.lift_fst]
      

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.lift, Limits, Limits.prod.fst, condition_assoc, kernel, kernel.condition_assoc, lift_fst, normalMonoOfMono, prod.lift, prod.lift_fst, zero_comp
-/
lemma pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b] :
    HasLimit (cospan a b) :=
  let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g))
      calc kernel.ι (prod.lift f g) ≫ f
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.fst := by rw [prod.lift_fst]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.fst := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp
  let ⟨b', hb'⟩ :=
KernelFork.IsLimit.lift' i' (kernel.ι (prod.lift f g))
      calc kernel.ι (prod.lift f g) ≫ g
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.snd := by rw [prod.lift_snd]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.snd := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp
  HasLimit.mk
    { cone :=
PullbackCone.mk a' b' by rw [dsimp% ha', dsimp% hb']
      isLimit :=
        PullbackCone.IsLimit.mk _
          (fun s =>
kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b)
              Limits.prod.hom_ext
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.fst =
                      PullbackCone.snd s ≫ b ≫ f := by simp only [prod.lift_fst, Category.assoc]
                  _ = PullbackCone.fst s ≫ a ≫ f := by rw [PullbackCone.condition_assoc]
                  _ = PullbackCone.fst s ≫ 0 := by rw [haf]
                  _ = 0 ≫ Limits.prod.fst := by rw [comp_zero, zero_comp])
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.snd =
                      PullbackCone.snd s ≫ b ≫ g := by
                    simp only [prod.lift_snd, Category.assoc]
                  _ = PullbackCone.snd s ≫ 0 := by rw [hbg]
                  _ = 0 ≫ Limits.prod.snd := by rw [comp_zero, zero_comp]))
          (fun s =>
(cancel_mono a).1 by
              rw [KernelFork.ι_ofι] at ha'
              simp [ha', PullbackCone.condition s])
          (fun s =>
(cancel_mono b).1 by
              rw [KernelFork.ι_ofι] at hb'
              simp [hb'])
          fun s m h₁ _ =>
(cancel_mono (kernel.ι (prod.lift f g))).1
            calc
              m ≫ kernel.ι (prod.lift f g) = m ≫ a' ≫ a := by
                congr
                exact ha'.symm
              _ = PullbackCone.fst s ≫ a := by rw [← Category.assoc, h₁]
              _ = PullbackCone.snd s ≫ b := PullbackCone.condition s
              _ =
                  kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) _ ≫
                    kernel.ι (prod.lift f g) := by rw [kernel.lift_ι]
               }

section

attribute [local instance] pullback_of_mono

/--
Definition of `P` / `P` 的定义

English:
abbreviation P
  signature: {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)]
  body: pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

中文:
缩写 P
  签名: {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)]
  定义体: pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)
-/
private abbrev P {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)] :
    C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasLimit_parallelPair` / 引理 `hasLimit_parallelPair`

English:
lemma hasLimit_parallelPair
  given: {X Y : C} (f g : X ⟶ Y)
  statement: HasLimit (parallelPair f g)
  proof: have huv : (pullback.fst _ _ : P f g ⟶ X) = pullback.snd _ _ :=
    calc
(pullback.fst _ _ : P f g ⟶ X) = pullback.fst _ _ ≫ 𝟙 _ := Eq.symm Category.comp_id _
      _ = pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.fst := by rw [prod.lift_fst]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Li

中文:
引理 hasLimit_parallelPair
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: HasLimit (parallelPair f g)
  证明: have huv : (pullback.fst _ _ : P f g ⟶ X) = pullback.snd _ _ :=
    calc
(pullback.fst _ _ : P f g ⟶ X) = pullback.fst _ _ ≫ 𝟙 _ := Eq.symm Category.comp_id _
      _ = pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.fst := by rw [prod.lift_fst]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Li

Depends on / 依赖: Category, Category.comp_id, Eq.symm, Limits, Limits.prod.fst, comp_id, condition_assoc, lift_fst, prod.lift, prod.lift_fst, pullback, pullback.condition_assoc, pullback.fst, pullback.snd
-/
lemma hasLimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  have huv : (pullback.fst _ _ : P f g ⟶ X) = pullback.snd _ _ :=
    calc
(pullback.fst _ _ : P f g ⟶ X) = pullback.fst _ _ ≫ 𝟙 _ := Eq.symm Category.comp_id _
      _ = pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.fst := by rw [prod.lift_fst]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Limits.prod.fst := by rw [pullback.condition_assoc]
      _ = pullback.snd _ _ := by rw [prod.lift_fst, Category.comp_id]
  have hvu : (pullback.fst _ _ : P f g ⟶ X) ≫ f = pullback.snd _ _ ≫ g :=
    calc
      (pullback.fst _ _ : P f g ⟶ X) ≫ f =
        pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.snd := by rw [prod.lift_snd]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Limits.prod.snd := by rw [pullback.condition_assoc]
      _ = pullback.snd _ _ ≫ g := by rw [prod.lift_snd]
  have huu : (pullback.fst _ _ : P f g ⟶ X) ≫ f = pullback.fst _ _ ≫ g := by rw [hvu, ← huv]
  HasLimit.mk
    { cone := Fork.ofι (pullback.fst _ _) huu
      isLimit :=
        Fork.IsLimit.mk _
          (fun s =>
pullback.lift (Fork.ι s) (Fork.ι s)
              Limits.prod.hom_ext (by simp only [prod.lift_fst, Category.assoc])
                (by simp only [prod.comp_lift, Fork.condition s]))
          (fun s => by simp) fun s m h =>
          pullback.hom_ext (by simpa only [pullback.lift_fst] using! h)
            (by simpa only [huv.symm, pullback.lift_fst] using! h) }

end

section

attribute [local instance] hasLimit_parallelPair

/-- A `NormalMonoCategory` category with finite products and kernels has all equalizers. -/
instance (priority := 100) hasEqualizers : HasEqualizers C :=
  hasEqualizers_of_hasLimit_parallelPair _

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_of_zero_cokernel` / 定理 `epi_of_zero_cokernel`

English:
theorem epi_of_zero_cokernel
  statement: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
    rw [Cofork.π_ofπ]; rw [zero_comp] at

中文:
定理 epi_of_zero_cokernel
  结论: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
    rw [Cofork.π_ofπ]; rw [zero_comp] at

Depends on / 依赖: Category, Category.assoc, Cofork, CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, cancel_epi, comp_zero, condition, equalizer, equalizer.condition, equalizer.lift, hn.symm, isIso_limit_cone_parallelPair_of_eq, normalMonoOfMono, zero_comp
-/
theorem epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0 by simp))) : Epi f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
    rw [Cofork.π_ofπ]; rw [zero_comp] at hn
    have : IsIso (equalizer.ι u v) := by apply isIso_limit_cone_parallelPair_of_eq hn.symm hl
    apply (cancel_epi (equalizer.ι u v)).1
    exact equalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/--
theorem `epi_of_zero_cancel` / 定理 `epi_of_zero_cancel`

English:
theorem epi_of_zero_cancel
  statement: {X Y : C} (f : X ⟶ Y)
  proof: epi_of_zero_cokernel f 0 zeroCokernelOfZeroCancel f hf

中文:
定理 epi_of_zero_cancel
  结论: {X Y : C} (f : X ⟶ Y)
  证明: epi_of_zero_cokernel f 0 zeroCokernelOfZeroCancel f hf

Depends on / 依赖: epi_of_zero_cokernel, zeroCokernelOfZeroCancel
-/
theorem epi_of_zero_cancel {X Y : C} (f : X ⟶ Y)
    (hf : forall (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) : Epi f :=
epi_of_zero_cokernel f 0 zeroCokernelOfZeroCancel f hf

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]

/--
lemma `preservesEpimorphisms_of_preservesCokernels` / 引理 `preservesEpimorphisms_of_preservesCokernels`

English:
lemma preservesEpimorphisms_of_preservesCokernels
  statement: (F : D ⥤ C) [F.PreservesZeroMorphisms]
  proof: epi_of_zero_cokernel _ _ IsColimit.equivIsoColimit (mapZeroCokernelCofork F f)
    (cokernel.zeroCokernelCofork f).mapIsColimit (cokernel.isColimitCoconeZeroCocone f) F

中文:
引理 preservesEpimorphisms_of_preservesCokernels
  结论: (F : D ⥤ C) [F.PreservesZeroMorphisms]
  证明: epi_of_zero_cokernel _ _ IsColimit.equivIsoColimit (mapZeroCokernelCofork F f)
    (cokernel.zeroCokernelCofork f).mapIsColimit (cokernel.isColimitCoconeZeroCocone f) F

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, cokernel, cokernel.isColimitCoconeZeroCocone, cokernel.zeroCokernelCofork, epi_of_zero_cokernel, equivIsoColimit, isColimitCoconeZeroCocone, mapIsColimit, mapZeroCokernelCofork, zeroCokernelCofork
-/
lemma preservesEpimorphisms_of_preservesCokernels (F : D ⥤ C) [F.PreservesZeroMorphisms]
    [forall {X Y : D} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    F.PreservesEpimorphisms where
  preserves f :=
epi_of_zero_cokernel _ _ IsColimit.equivIsoColimit (mapZeroCokernelCofork F f)
    (cokernel.zeroCokernelCofork f).mapIsColimit (cokernel.isColimitCoconeZeroCocone f) F

end

end CategoryTheory.NormalMonoCategory

namespace CategoryTheory.NormalEpiCategory

variable [HasFiniteCoproducts C] [HasCokernels C] [IsNormalEpiCategory C]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pushout_of_epi` / 引理 `pushout_of_epi`

English:
lemma pushout_of_epi
  given: {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b]
  proof: let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g))
      calc
        f ≫ cokernel.π (coprod.desc f g) =
            coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
    

中文:
引理 pushout_of_epi
  条件: {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b]
  证明: let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g))
      calc
        f ≫ cokernel.π (coprod.desc f g) =
            coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
    

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, HasZeroMorphisms, HasZeroMorphisms.comp_zero, IsColimit, cokernel, cokernel.condition, comp_zero, condition, coprod, coprod.desc, coprod.inl, coprod.inl_desc_assoc, inl_desc_assoc, normalEpiOfEpi
-/
lemma pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b] :
    HasColimit (span a b) :=
  let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g))
      calc
        f ≫ cokernel.π (coprod.desc f g) =
            coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inl_desc_assoc]
        _ = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
  let ⟨b', hb'⟩ :=
CokernelCofork.IsColimit.desc' i' (cokernel.π (coprod.desc f g))
      calc
        g ≫ cokernel.π (coprod.desc f g) =
            coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inr_desc_assoc]
        _ = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
  HasColimit.mk
    { cocone :=
PushoutCocone.mk a' b' by
          simp only [Cofork.π_ofπ] at ha' hb'
          rw [ha']; rw [hb']
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s =>
cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s)
              coprod.hom_ext
                (calc
                  coprod.inl ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      f ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inl_desc_assoc]
                  _ = f ≫ a ≫ PushoutCocone.inl s := by rw [PushoutCocone.condition]
                  _ = 0 ≫ PushoutCocone.inl s := by rw [← Category.assoc, eq_whisker hfa]
                  _ = coprod.inl ≫ 0 := by rw [comp_zero, zero_comp])
                (calc
                  coprod.inr ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      g ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inr_desc_assoc]
                  _ = 0 ≫ PushoutCocone.inr s := by rw [← Category.assoc, eq_whisker hgb]
                  _ = coprod.inr ≫ 0 := by rw [comp_zero, zero_comp]))
          (fun s =>
(cancel_epi a).1 by
              rw [CokernelCofork.π_ofπ] at ha'
              have reassoced {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : a ≫ a' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker ha']
              simp [reassoced, PushoutCocone.condition s])
          (fun s =>
(cancel_epi b).1 by
              rw [CokernelCofork.π_ofπ] at hb'
              have reassoced' {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : b ≫ b' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker hb']
              simp [reassoced'])
          fun s m h₁ _ =>
(cancel_epi (cokernel.π (coprod.desc f g))).1
            calc
              cokernel.π (coprod.desc f g) ≫ m = (a ≫ a') ≫ m := by
                congr
                exact ha'.symm
              _ = a ≫ PushoutCocone.inl s := by rw [Category.assoc, h₁]
              _ = b ≫ PushoutCocone.inr s := PushoutCocone.condition s
              _ =
                  cokernel.π (coprod.desc f g) ≫
                    cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) _ := by
                rw [cokernel.π_desc]
               }

section

attribute [local instance] pushout_of_epi

/--
Definition of `Q` / `Q` 的定义

English:
abbreviation Q
  signature: {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)]
  body: pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

中文:
缩写 Q
  签名: {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)]
  定义体: pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)
-/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)] :
    C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasColimit_parallelPair` / 引理 `hasColimit_parallelPair`

English:
lemma hasColimit_parallelPair
  given: {X Y : C} (f g : X ⟶ Y)
  statement: HasColimit (parallelPair f g)
  proof: have huv : (pushout.inl _ _ : Y ⟶ Q f g) = pushout.inr _ _ :=
    calc
(pushout.inl _ _ : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl _ _ := Eq.symm Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.

中文:
引理 hasColimit_parallelPair
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: HasColimit (parallelPair f g)
  证明: have huv : (pushout.inl _ _ : Y ⟶ Q f g) = pushout.inr _ _ :=
    calc
(pushout.inl _ _ : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl _ _ := Eq.symm Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Eq.symm, condition, coprod, coprod.desc, coprod.inl, coprod.inl_desc, id_comp, inl_desc, pushout, pushout.condition, pushout.inl, pushout.inr
-/
lemma hasColimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  have huv : (pushout.inl _ _ : Y ⟶ Q f g) = pushout.inr _ _ :=
    calc
(pushout.inl _ _ : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl _ _ := Eq.symm Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr _ _ := by
        simp only [Category.assoc, pushout.condition]
      _ = pushout.inr _ _ := by rw [coprod.inl_desc, Category.id_comp]
  have hvu : f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = g ≫ pushout.inr _ _ :=
    calc
      f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by
        rw [coprod.inr_desc]
      _ = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr _ _ := by
        simp only [Category.assoc, pushout.condition]
      _ = g ≫ pushout.inr _ _ := by rw [coprod.inr_desc]
  have huu : f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = g ≫ pushout.inl _ _ := by rw [hvu, huv]
  HasColimit.mk
    { cocone := Cofork.ofπ (pushout.inl _ _) huu
      isColimit :=
        Cofork.IsColimit.mk _
          (fun s =>
pushout.desc (Cofork.π s) (Cofork.π s)
              coprod.hom_ext (by simp only [coprod.inl_desc_assoc])
                (by simp only [coprod.desc_comp, Cofork.condition s]))
          (fun s => by simp only [pushout.inl_desc, Cofork.π_ofπ]) fun s m h =>
          pushout.hom_ext (by simpa only [pushout.inl_desc] using! h)
            (by simpa only [huv.symm, pushout.inl_desc] using! h) }

end

section

attribute [local instance] hasColimit_parallelPair

/-- A `NormalEpiCategory` category with finite coproducts and cokernels has all coequalizers. -/
instance (priority := 100) hasCoequalizers : HasCoequalizers C :=
  hasCoequalizers_of_hasColimit_parallelPair _

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_of_zero_kernel` / 定理 `mono_of_zero_kernel`

English:
theorem mono_of_zero_kernel
  statement: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have reassoced {W : C} (h : coequalizer u v ⟶ W) : w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hw]
    have hwf : w ≫ f = 0 := 

中文:
定理 mono_of_zero_kernel
  结论: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have reassoced {W : C} (h : coequalizer u v ⟶ W) : w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hw]
    have hwf : w ≫ f = 0 := 

Depends on / 依赖: Category, Category.assoc, HasZeroMorphisms, HasZeroMorphisms.comp_zero, IsLimit, KernelFork, KernelFork.IsLimit.lift, coequalizer, coequalizer.desc, comp_zero, eq_whisker, isIso_colimit_cocone_parallelPair_of, normalEpiOfEpi, reassoced, zero_comp
-/
theorem mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by simp))) : Mono f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have reassoced {W : C} (h : coequalizer u v ⟶ W) : w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hw]
    have hwf : w ≫ f = 0 := by rw [← hm, reassoced, zero_comp]
    obtain ⟨n, hn⟩ := KernelFork.IsLimit.lift' l _ hwf
    rw [Fork.ι_ofι]; rw [HasZeroMorphisms.comp_zero] at hn
    have : IsIso (coequalizer.π u v) := by
      apply isIso_colimit_cocone_parallelPair_of_eq hn.symm hl
    apply (cancel_mono (coequalizer.π u v)).1
    exact coequalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/--
theorem `mono_of_cancel_zero` / 定理 `mono_of_cancel_zero`

English:
theorem mono_of_cancel_zero
  statement: {X Y : C} (f : X ⟶ Y)
  proof: mono_of_zero_kernel f 0 zeroKernelOfCancelZero f hf

中文:
定理 mono_of_cancel_zero
  结论: {X Y : C} (f : X ⟶ Y)
  证明: mono_of_zero_kernel f 0 zeroKernelOfCancelZero f hf

Depends on / 依赖: mono_of_zero_kernel, zeroKernelOfCancelZero
-/
theorem mono_of_cancel_zero {X Y : C} (f : X ⟶ Y)
    (hf : forall (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) : Mono f :=
mono_of_zero_kernel f 0 zeroKernelOfCancelZero f hf

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]

/--
lemma `preservesMonomorphisms_of_preservesKernels` / 引理 `preservesMonomorphisms_of_preservesKernels`

English:
lemma preservesMonomorphisms_of_preservesKernels
  statement: (F : D ⥤ C) [F.PreservesZeroMorphisms]
  proof: mono_of_zero_kernel _ _ IsLimit.equivIsoLimit (mapZeroKernelFork F f)
    (kernel.zeroKernelFork f).mapIsLimit (kernel.isLimitConeZeroCone f) F

中文:
引理 preservesMonomorphisms_of_preservesKernels
  结论: (F : D ⥤ C) [F.PreservesZeroMorphisms]
  证明: mono_of_zero_kernel _ _ IsLimit.equivIsoLimit (mapZeroKernelFork F f)
    (kernel.zeroKernelFork f).mapIsLimit (kernel.isLimitConeZeroCone f) F

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, equivIsoLimit, isLimitConeZeroCone, kernel, kernel.isLimitConeZeroCone, kernel.zeroKernelFork, mapIsLimit, mapZeroKernelFork, mono_of_zero_kernel, zeroKernelFork
-/
lemma preservesMonomorphisms_of_preservesKernels (F : D ⥤ C) [F.PreservesZeroMorphisms]
    [forall {X Y : D} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    F.PreservesMonomorphisms where
  preserves f :=
mono_of_zero_kernel _ _ IsLimit.equivIsoLimit (mapZeroKernelFork F f)
    (kernel.zeroKernelFork f).mapIsLimit (kernel.isLimitConeZeroCone f) F

end

end CategoryTheory.NormalEpiCategory
