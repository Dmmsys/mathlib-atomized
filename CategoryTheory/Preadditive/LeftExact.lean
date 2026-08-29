/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Left exactness of functors between preadditive categories

We show that a functor is left exact in the sense that it preserves finite limits, if it
preserves kernels. The dual result holds for right exact functors and cokernels.

## Main results

* We first derive preservation of binary products in the lemma
  `preservesBinaryProducts_of_preservesKernels`,
* then show the preservation of equalizers in `preservesEqualizer_of_preservesKernels`,
* and then derive the preservation of all finite limits with the usual construction.

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (F : C ⥤ D) [PreservesZeroMorphisms F]

section FiniteLimits

/--
Definition of `isLimitMapConeBinaryFanOfPreservesKernels` / `isLimitMapConeBinaryFanOfPreservesKernels` 的定义

English:
definition isLimitMapConeBinaryFanOfPreservesKernels
  signature: {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
  body: by
  let bc := BinaryBicone.ofLimitCone i
  let presf : PreservesLimit (parallelPair bc.snd 0) F := by simpa
  let hf : IsLimit bc.sndKernelFork := BinaryBicone.isLimitSndKernelFork i
  exact (isLimitMapConeBinaryFanEquiv F π₁ π₂).invFun
    (BinaryBicone.isBilimitOfKernelInl (F.mapBinaryBicone bc)


中文:
定义 isLimitMapConeBinaryFanOfPreservesKernels
  签名: {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
  定义体: by
  let bc := BinaryBicone.ofLimitCone i
  let presf : PreservesLimit (parallelPair bc.snd 0) F := by simpa
  let hf : IsLimit bc.sndKernelFork := BinaryBicone.isLimitSndKernelFork i
  exact (isLimitMapConeBinaryFanEquiv F π₁ π₂).invFun
    (BinaryBicone.isBilimitOfKernelInl (F.mapBinaryBicone bc)


Depends on / 依赖: BinaryBicone, BinaryBicone.isBilimitOfKernelInl, BinaryBicone.isLimitSndKernelFork, BinaryBicone.ofLimitCone, F.mapBinaryBicone, IsLimit, PreservesLimit, bc.inl_snd, bc.snd, bc.sndKernelFork, inl_snd, invFun, isBilimitOfKernelInl, isLimit, isLimitMapConeBinaryFanEquiv, isLimitMapConeForkEquiv, isLimitOfPreserves, isLimitSndKernelFork, mapBinaryBicone, ofLimitCone
-/
def isLimitMapConeBinaryFanOfPreservesKernels {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
    [PreservesLimit (parallelPair π₂ 0) F] (i : IsLimit (BinaryFan.mk π₁ π₂)) :
    IsLimit (F.mapCone (BinaryFan.mk π₁ π₂)) := by
  let bc := BinaryBicone.ofLimitCone i
  let presf : PreservesLimit (parallelPair bc.snd 0) F := by simpa
  let hf : IsLimit bc.sndKernelFork := BinaryBicone.isLimitSndKernelFork i
  exact (isLimitMapConeBinaryFanEquiv F π₁ π₂).invFun
    (BinaryBicone.isBilimitOfKernelInl (F.mapBinaryBicone bc)
    (isLimitMapConeForkEquiv' F bc.inl_snd (isLimitOfPreserves F hf))).isLimit

/--
lemma `preservesBinaryProduct_of_preservesKernels` / 引理 `preservesBinaryProduct_of_preservesKernels`

English:
lemma preservesBinaryProduct_of_preservesKernels
  proof: ⟨IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cone.functoriality _ F).mapIso (isoBinaryFanMk c).symm)⟩

中文:
引理 preservesBinaryProduct_of_preservesKernels
  证明: ⟨IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cone.functoriality _ F).mapIso (isoBinaryFanMk c).symm)⟩

Depends on / 依赖: Cone.functoriality, IsLimit, IsLimit.ofIsoLimit, functoriality, isLimitMapConeBinaryFanOfPreservesKernels, isoBinaryFanMk, mapIso, ofIsoLimit
-/
lemma preservesBinaryProduct_of_preservesKernels
    [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : C} :
    PreservesLimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cone.functoriality _ F).mapIso (isoBinaryFanMk c).symm)⟩

attribute [local instance] preservesBinaryProduct_of_preservesKernels

/--
lemma `preservesBinaryProducts_of_preservesKernels` / 引理 `preservesBinaryProducts_of_preservesKernels`

English:
lemma preservesBinaryProducts_of_preservesKernels
  proof: preservesLimit_of_iso_diagram F (diagramIsoPair _).symm

中文:
引理 preservesBinaryProducts_of_preservesKernels
  证明: preservesLimit_of_iso_diagram F (diagramIsoPair _).symm

Depends on / 依赖: diagramIsoPair, preservesLimit_of_iso_diagram
-/
lemma preservesBinaryProducts_of_preservesKernels
    [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit := preservesLimit_of_iso_diagram F (diagramIsoPair _).symm

attribute [local instance] preservesBinaryProducts_of_preservesKernels

variable [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesEqualizer_of_preservesKernels` / 引理 `preservesEqualizer_of_preservesKernels`

English:
lemma preservesEqualizer_of_preservesKernels
  proof: by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor; intro c i
  let c' := isLimitKernelForkOfFork (i.ofIsoLimit (Fork.isoForkOfι c))
  dsimp only [kernelForkOfFork_ofι] at c'
  let iFc := isLimitForkMapOfIsLimit' F _ c'


中文:
引理 preservesEqualizer_of_preservesKernels
  证明: by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor; intro c i
  let c' := isLimitKernelForkOfFork (i.ofIsoLimit (Fork.isoForkOfι c))
  dsimp only [kernelForkOfFork_ofι] at c'
  let iFc := isLimitForkMapOfIsLimit' F _ c'


Depends on / 依赖: Cone.functoriality, F.map, Fork.condition, Fork.isoForkOf, IsLimit, IsLimit.ofIsoLimit, additive_of_preservesBinaryBiproducts, condition, functoriality, i.ofIsoLimit, invFun, isLimitForkMapOfIsLimit, isLimitKernelForkOfFork, isLimitMapConeForkEquiv, mapIso, ofIsoLimit, parallelPair, preservesBinaryBiproducts_of_preservesBinaryProducts
-/
lemma preservesEqualizer_of_preservesKernels
    [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F]
    {X Y : C} (f g : X ⟶ Y) : PreservesLimit (parallelPair f g) F := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor; intro c i
  let c' := isLimitKernelForkOfFork (i.ofIsoLimit (Fork.isoForkOfι c))
  dsimp only [kernelForkOfFork_ofι] at c'
  let iFc := isLimitForkMapOfIsLimit' F _ c'
  constructor
  apply IsLimit.ofIsoLimit _ ((Cone.functoriality _ F).mapIso (Fork.isoForkOfι c).symm)
  apply (isLimitMapConeForkEquiv F (Fork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.eqOfHomEq F.map_sub rfl
  exact
    IsLimit.ofIsoLimit
      (isLimitForkOfKernelFork ((IsLimit.postcomposeHomEquiv p _).symm iFc))
      (Fork.ext (Iso.refl _) (by simp [p]))

/--
lemma `preservesEqualizers_of_preservesKernels` / 引理 `preservesEqualizers_of_preservesKernels`

English:
lemma preservesEqualizers_of_preservesKernels
  proof: by
    let := preservesEqualizer_of_preservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm

中文:
引理 preservesEqualizers_of_preservesKernels
  证明: by
    let := preservesEqualizer_of_preservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm

Depends on / 依赖: K.map, WalkingParallelPairHom, WalkingParallelPairHom.left, WalkingParallelPairHom.right, diagramIsoParallelPair, preservesEqualizer_of_preservesKernels, preservesLimit_of_iso_diagram
-/
lemma preservesEqualizers_of_preservesKernels
    [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := by
    let := preservesEqualizer_of_preservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm

/--
lemma `preservesFiniteLimits_of_preservesKernels` / 引理 `preservesFiniteLimits_of_preservesKernels`

English:
lemma preservesFiniteLimits_of_preservesKernels
  statement: [HasFiniteProducts C] [HasEqualizers C]
  proof: have := preservesEqualizers_of_preservesKernels F
  have := preservesTerminalObject_of_preservesZeroMorphisms F
  have := preservesLimitsOfShape_pempty_of_preservesTerminal F
  have : PreservesFiniteProducts F := .of_preserves_binary_and_terminal F
  preservesFiniteLimits_of_preservesEqualizers_and_

中文:
引理 preservesFiniteLimits_of_preservesKernels
  结论: [HasFiniteProducts C] [HasEqualizers C]
  证明: have := preservesEqualizers_of_preservesKernels F
  have := preservesTerminalObject_of_preservesZeroMorphisms F
  have := preservesLimitsOfShape_pempty_of_preservesTerminal F
  have : PreservesFiniteProducts F := .of_preserves_binary_and_terminal F
  preservesFiniteLimits_of_preservesEqualizers_and_

Depends on / 依赖: PreservesFiniteProducts, of_preserves_binary_and_terminal, preservesEqualizers_of_preservesKernels, preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts, preservesLimitsOfShape_pempty_of_preservesTerminal, preservesTerminalObject_of_preservesZeroMorphisms
-/
lemma preservesFiniteLimits_of_preservesKernels [HasFiniteProducts C] [HasEqualizers C]
    [HasZeroObject C] [HasZeroObject D] [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesFiniteLimits F :=
  have := preservesEqualizers_of_preservesKernels F
  have := preservesTerminalObject_of_preservesZeroMorphisms F
  have := preservesLimitsOfShape_pempty_of_preservesTerminal F
  have : PreservesFiniteProducts F := .of_preserves_binary_and_terminal F
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts F

end FiniteLimits

section FiniteColimits

/--
Definition of `isColimitMapCoconeBinaryCofanOfPreservesCokernels` / `isColimitMapCoconeBinaryCofanOfPreservesCokernels` 的定义

English:
definition isColimitMapCoconeBinaryCofanOfPreservesCokernels
  signature: {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
  body: by
  let bc := BinaryBicone.ofColimitCocone i
  let presf : PreservesColimit (parallelPair bc.inr 0) F := by simpa
  let hf : IsColimit bc.inrCokernelCofork := BinaryBicone.isColimitInrCokernelCofork i
  exact
    (isColimitMapCoconeBinaryCofanEquiv F ι₁ ι₂).invFun
      (BinaryBicone.isBilimitOfCok

中文:
定义 isColimitMapCoconeBinaryCofanOfPreservesCokernels
  签名: {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
  定义体: by
  let bc := BinaryBicone.ofColimitCocone i
  let presf : PreservesColimit (parallelPair bc.inr 0) F := by simpa
  let hf : IsColimit bc.inrCokernelCofork := BinaryBicone.isColimitInrCokernelCofork i
  exact
    (isColimitMapCoconeBinaryCofanEquiv F ι₁ ι₂).invFun
      (BinaryBicone.isBilimitOfCok

Depends on / 依赖: BinaryBicone, BinaryBicone.isBilimitOfCokernelFst, BinaryBicone.isColimitInrCokernelCofork, BinaryBicone.ofColimitCocone, F.mapBinaryBicone, IsColimit, PreservesColimit, bc.inr, bc.inrCokernelCofork, bc.inr_fst, inrCokernelCofork, inr_fst, invFun, isBilimitOfCokernelFst, isColimit, isColimitInrCokernelCofork, isColimitMapCoconeBinaryCofanEquiv, isColimitMapCoconeCoforkEquiv, isColimitOfPreserves, mapBinaryBicone
-/
def isColimitMapCoconeBinaryCofanOfPreservesCokernels {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
    [PreservesColimit (parallelPair ι₂ 0) F] (i : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    IsColimit (F.mapCocone (BinaryCofan.mk ι₁ ι₂)) := by
  let bc := BinaryBicone.ofColimitCocone i
  let presf : PreservesColimit (parallelPair bc.inr 0) F := by simpa
  let hf : IsColimit bc.inrCokernelCofork := BinaryBicone.isColimitInrCokernelCofork i
  exact
    (isColimitMapCoconeBinaryCofanEquiv F ι₁ ι₂).invFun
      (BinaryBicone.isBilimitOfCokernelFst (F.mapBinaryBicone bc)
          (isColimitMapCoconeCoforkEquiv' F bc.inr_fst (isColimitOfPreserves F hf))).isColimit

/--
lemma `preservesCoproduct_of_preservesCokernels` / 引理 `preservesCoproduct_of_preservesCokernels`

English:
lemma preservesCoproduct_of_preservesCokernels
  proof: ⟨IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocone.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)⟩

中文:
引理 preservesCoproduct_of_preservesCokernels
  证明: ⟨IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocone.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)⟩

Depends on / 依赖: Cocone, Cocone.functoriality, IsColimit, IsColimit.ofIsoColimit, functoriality, isColimitMapCoconeBinaryCofanOfPreservesCokernels, isoBinaryCofanMk, mapIso, ofIsoColimit
-/
lemma preservesCoproduct_of_preservesCokernels
    [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocone.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)⟩

attribute [local instance] preservesCoproduct_of_preservesCokernels

/--
lemma `preservesBinaryCoproducts_of_preservesCokernels` / 引理 `preservesBinaryCoproducts_of_preservesCokernels`

English:
lemma preservesBinaryCoproducts_of_preservesCokernels
  proof: preservesColimit_of_iso_diagram F (diagramIsoPair _).symm

中文:
引理 preservesBinaryCoproducts_of_preservesCokernels
  证明: preservesColimit_of_iso_diagram F (diagramIsoPair _).symm

Depends on / 依赖: diagramIsoPair, preservesColimit_of_iso_diagram
-/
lemma preservesBinaryCoproducts_of_preservesCokernels
    [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit := preservesColimit_of_iso_diagram F (diagramIsoPair _).symm

attribute [local instance] preservesBinaryCoproducts_of_preservesCokernels

variable [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesCoequalizer_of_preservesCokernels` / 引理 `preservesCoequalizer_of_preservesCokernels`

English:
lemma preservesCoequalizer_of_preservesCokernels
  proof: by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor
  intro c i
  let c' := isColimitCokernelCoforkOfCofork (i.ofIsoColimit (Cofork.isoCoforkOfπ c))
  dsimp only [cokernelCoforkOfCofork_ofπ] at c'
  let iFc := isColimit

中文:
引理 preservesCoequalizer_of_preservesCokernels
  证明: by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor
  intro c i
  let c' := isColimitCokernelCoforkOfCofork (i.ofIsoColimit (Cofork.isoCoforkOfπ c))
  dsimp only [cokernelCoforkOfCofork_ofπ] at c'
  let iFc := isColimit

Depends on / 依赖: Cocone, Cocone.functoriality, Cofork, Cofork.condition, Cofork.isoCoforkOf, IsColimit, IsColimit.ofIsoColimit, additive_of_preservesBinaryBiproducts, condition, functoriality, i.ofIsoColimit, invFun, isColimitCoforkMapOfIsColimit, isColimitCokernelCoforkOfCofork, isColimitMapCoconeCoforkEquiv, mapIso, ofIsoColimit, preservesBinaryBiproducts_of_preservesBinaryCoproducts
-/
lemma preservesCoequalizer_of_preservesCokernels
    [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) F := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := additive_of_preservesBinaryBiproducts F
  constructor
  intro c i
  let c' := isColimitCokernelCoforkOfCofork (i.ofIsoColimit (Cofork.isoCoforkOfπ c))
  dsimp only [cokernelCoforkOfCofork_ofπ] at c'
  let iFc := isColimitCoforkMapOfIsColimit' F _ c'
  constructor
  apply
    IsColimit.ofIsoColimit _ ((Cocone.functoriality _ F).mapIso (Cofork.isoCoforkOfπ c).symm)
  apply (isColimitMapCoconeCoforkEquiv F (Cofork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  exact
    IsColimit.ofIsoColimit
      (isColimitCoforkOfCokernelCofork ((IsColimit.precomposeHomEquiv p.symm _).symm iFc))
      (Cofork.ext (Iso.refl _) (by simp [p]))

/--
lemma `preservesCoequalizers_of_preservesCokernels` / 引理 `preservesCoequalizers_of_preservesCokernels`

English:
lemma preservesCoequalizers_of_preservesCokernels
  proof: by
    let := preservesCoequalizer_of_preservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm

中文:
引理 preservesCoequalizers_of_preservesCokernels
  证明: by
    let := preservesCoequalizer_of_preservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm

Depends on / 依赖: K.map, Limits, Limits.WalkingParallelPairHom.left, Limits.WalkingParallelPairHom.right, WalkingParallelPairHom, diagramIsoParallelPair, preservesCoequalizer_of_preservesCokernels, preservesColimit_of_iso_diagram
-/
lemma preservesCoequalizers_of_preservesCokernels
    [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape WalkingParallelPair F where
  preservesColimit {K} := by
    let := preservesCoequalizer_of_preservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm

/--
lemma `preservesFiniteColimits_of_preservesCokernels` / 引理 `preservesFiniteColimits_of_preservesCokernels`

English:
lemma preservesFiniteColimits_of_preservesCokernels
  statement: [HasFiniteCoproducts C] [HasCoequalizers C]
  proof: by
  let := preservesCoequalizers_of_preservesCokernels F
  let := preservesInitialObject_of_preservesZeroMorphisms F
  let := preservesColimitsOfShape_pempty_of_preservesInitial F
  let : PreservesFiniteCoproducts F :=
    ⟨fun _ => PreservesFiniteCoproducts.of_preserves_binary_and_initial F _⟩
  e

中文:
引理 preservesFiniteColimits_of_preservesCokernels
  结论: [HasFiniteCoproducts C] [HasCoequalizers C]
  证明: by
  let := preservesCoequalizers_of_preservesCokernels F
  let := preservesInitialObject_of_preservesZeroMorphisms F
  let := preservesColimitsOfShape_pempty_of_preservesInitial F
  let : PreservesFiniteCoproducts F :=
    ⟨fun _ => PreservesFiniteCoproducts.of_preserves_binary_and_initial F _⟩
  e

Depends on / 依赖: PreservesFiniteCoproducts, PreservesFiniteCoproducts.of_preserves_binary_and_initial, of_preserves_binary_and_initial, preservesCoequalizers_of_preservesCokernels, preservesColimitsOfShape_pempty_of_preservesInitial, preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts, preservesInitialObject_of_preservesZeroMorphisms
-/
lemma preservesFiniteColimits_of_preservesCokernels [HasFiniteCoproducts C] [HasCoequalizers C]
    [HasZeroObject C] [HasZeroObject D]
    [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F := by
  let := preservesCoequalizers_of_preservesCokernels F
  let := preservesInitialObject_of_preservesZeroMorphisms F
  let := preservesColimitsOfShape_pempty_of_preservesInitial F
  let : PreservesFiniteCoproducts F :=
    ⟨fun _ => PreservesFiniteCoproducts.of_preserves_binary_and_initial F _⟩
  exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts F

end FiniteColimits

end Functor

end CategoryTheory
