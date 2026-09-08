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

/-- A functor between preadditive categories which preserves kernels preserves that an
arbitrary binary fan is a limit.
-/
/-
**CategoryTheory.Functor.isLimitMapConeBinaryFanOfPreservesKernels** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLimitMapConeBinaryFanOfPreservesKernels {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z
 ⟶ Y) [PreservesLimit (parallelPair π₂ 0) F] (i : IsLimit (BinaryFan.mk π₁ π₂)) 
: IsLimit (F.mapCone (BinaryFan.mk π₁ π₂))
参数：π₁ : Z ⟶ X；π₂ : Z ⟶ Y；parallelPair π₂ 0；i : IsLimit (BinaryFan.mk π₁ π₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between preadditive categories which preserves kernels preserves that 
an
arbitrary binary fan is a limit.
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

/-- A kernel-preserving functor between preadditive categories preserves any pair being a limit. -/
/-
**CategoryTheory.Functor.preservesBinaryProduct_of_preservesKernels** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesBinaryProduct_of_preservesKernels [forall {X Y} (f : X ⟶ Y), Pres
ervesLimit (parallelPair f 0) F] {X Y : C} : PreservesLimit (pair X Y) F where p
reserves {c} hc
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel-preserving functor between preadditive categories preserves any pair be
ing a limit.
-/
lemma preservesBinaryProduct_of_preservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : C} :
    PreservesLimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cone.functoriality _ F).mapIso (isoBinaryFanMk c).symm)⟩

attribute [local instance] preservesBinaryProduct_of_preservesKernels

/-- A kernel-preserving functor between preadditive categories preserves binary products. -/
/-
**CategoryTheory.Functor.preservesBinaryProducts_of_preservesKernels** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesBinaryProducts_of_preservesKernels [forall {X Y} (f : X ⟶ Y), Pre
servesLimit (parallelPair f 0) F] : PreservesLimitsOfShape (Discrete WalkingPair
) F where preservesLimit
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用引理 `CategoryTheory.Functor.preservesBinaryProduct_of_preservesKernels`：prese
rvesBinaryProduct_of_preservesKernels [forall {X Y} (f : X ⟶ Y), PreservesLimit 
(parallelPair f 0) F] {X Y : C} : PreservesLimit (pair …

--- 原说明 ---
A kernel-preserving functor between preadditive categories preserves binary prod
ucts.
-/
lemma preservesBinaryProducts_of_preservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit := preservesLimit_of_iso_diagram F (diagramIsoPair _).symm

attribute [local instance] preservesBinaryProducts_of_preservesKernels

variable [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels. -/
/-
**CategoryTheory.Functor.preservesEqualizer_of_preservesKernels** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEqualizer_of_preservesKernels [forall {X Y} (f : X ⟶ Y), Preserve
sLimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) : PreservesLimit (parallelP
air f g) F
参数：f : X ⟶ Y；parallelPair f 0；f g : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProduc
ts`：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfShape
 (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where p…
· 使用引理 `CategoryTheory.Functor.preservesBinaryProducts_of_preservesKernels`：pres
ervesBinaryProducts_of_preservesKernels [forall {X Y} (f : X ⟶ Y), PreservesLimi
t (parallelPair f 0) F] : PreservesLimitsOfShape (Discre…
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Functor.map_sub`：map_sub {X Y : C} {f g : X ⟶ Y} : F.map 
(f - g) = F.map f - F.map g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels.
-/
lemma preservesEqualizer_of_preservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F]
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

/-- A functor between preadditive categories preserves all equalizers if it preserves all kernels.
-/
/-
**CategoryTheory.Functor.preservesEqualizers_of_preservesKernels** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesEqualizers_of_preservesKernels [forall {X Y} (f : X ⟶ Y), Preserv
esLimit (parallelPair f 0) F] : PreservesLimitsOfShape WalkingParallelPair F whe
re preservesLimit {K}
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesEqualizer_of_preservesKernels`：preserves
Equalizer_of_preservesKernels [forall {X Y} (f : X ⟶ Y), PreservesLimit (paralle
lPair f 0) F] {X Y : C} (f g : X ⟶ Y) : PreservesLi…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
A functor between preadditive categories preserves all equalizers if it preserve
s all kernels.
-/
lemma preservesEqualizers_of_preservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := by
    let := preservesEqualizer_of_preservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
/-
**CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteLimits_of_preservesKernels [HasFiniteProducts C] [HasEquali
zers C] [HasZeroObject C] [HasZeroObject D] [forall {X Y} (f : X ⟶ Y), Preserves
Limit (parallelPair f 0) F] : PreservesFiniteLimits F
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesEqualizers_of_preservesKernels`：preserve
sEqualizers_of_preservesKernels [forall {X Y} (f : X ⟶ Y), PreservesLimit (paral
lelPair f 0) F] : PreservesLimitsOfShape WalkingPara…
· 使用引理 `CategoryTheory.Functor.preservesTerminalObject_of_preservesZeroMorphisms
`：preservesTerminalObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
 PreservesLimit (Functor.empty.{0} C) F
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
`：preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.em
pty.{0} C) G] : PreservesLimitsOfShape (Discrete PEmpty.{1}) G…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Functor.preservesBinaryProducts_of_preservesKernels`：pres
ervesBinaryProducts_of_preservesKernels [forall {X Y} (f : X ⟶ Y), PreservesLimi
t (parallelPair f 0) F] : PreservesLimitsOfShape (Discre…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesEqualizers_and_f
initeProducts`：preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [
HasEqualizers C] [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape …

--- 原说明 ---
A functor between preadditive categories which preserves kernels preserves all f
inite limits.
-/
lemma preservesFiniteLimits_of_preservesKernels [HasFiniteProducts C] [HasEqualizers C]
    [HasZeroObject C] [HasZeroObject D] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesFiniteLimits F :=
  have := preservesEqualizers_of_preservesKernels F
  have := preservesTerminalObject_of_preservesZeroMorphisms F
  have := preservesLimitsOfShape_pempty_of_preservesTerminal F
  have : PreservesFiniteProducts F := .of_preserves_binary_and_terminal F
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts F

end FiniteLimits

section FiniteColimits

/-- A functor between preadditive categories which preserves cokernels preserves finite coproducts.
-/
/-
**CategoryTheory.Functor.isColimitMapCoconeBinaryCofanOfPreservesCokernels** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isColimitMapCoconeBinaryCofanOfPreservesCokernels {X Y Z : C} (ι₁ : X ⟶ Z)
 (ι₂ : Y ⟶ Z) [PreservesColimit (parallelPair ι₂ 0) F] (i : IsColimit (BinaryCof
an.mk ι₁ ι₂)) : IsColimit (F.mapCocone (BinaryCofan.mk ι₁ ι₂))
参数：ι₁ : X ⟶ Z；ι₂ : Y ⟶ Z；parallelPair ι₂ 0；i : IsColimit (BinaryCofan.mk ι₁ ι₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between preadditive categories which preserves cokernels preserves fin
ite coproducts.
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

/-- A cokernel-preserving functor between preadditive categories preserves any pair being
a colimit. -/
/-
**CategoryTheory.Functor.preservesCoproduct_of_preservesCokernels** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesCoproduct_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), Preser
vesColimit (parallelPair f 0) F] {X Y : C} : PreservesColimit (pair X Y) F where
 preserves {c} hc
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cokernel-preserving functor between preadditive categories preserves any pair 
being
a colimit.
-/
lemma preservesCoproduct_of_preservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocone.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)⟩

attribute [local instance] preservesCoproduct_of_preservesCokernels

/-- A cokernel-preserving functor between preadditive categories preserves binary coproducts. -/
/-
**CategoryTheory.Functor.preservesBinaryCoproducts_of_preservesCokernels** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesBinaryCoproducts_of_preservesCokernels [forall {X Y} (f : X ⟶ Y),
 PreservesColimit (parallelPair f 0) F] : PreservesColimitsOfShape (Discrete Wal
kingPair) F where preservesColimit
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
· 使用引理 `CategoryTheory.Functor.preservesCoproduct_of_preservesCokernels`：preserv
esCoproduct_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), PreservesColimit (p
arallelPair f 0) F] {X Y : C} : PreservesColimit (pai…

--- 原说明 ---
A cokernel-preserving functor between preadditive categories preserves binary co
products.
-/
lemma preservesBinaryCoproducts_of_preservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit := preservesColimit_of_iso_diagram F (diagramIsoPair _).symm

attribute [local instance] preservesBinaryCoproducts_of_preservesCokernels

variable [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor between preadditive categories preserves the coequalizer of two
morphisms if it preserves all cokernels. -/
/-
**CategoryTheory.Functor.preservesCoequalizer_of_preservesCokernels** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesCoequalizer_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), Pres
ervesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) : PreservesColimit (p
arallelPair f g) F
参数：f : X ⟶ Y；parallelPair f 0；f g : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoprod
ucts`：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F whe…
· 使用引理 `CategoryTheory.Functor.preservesBinaryCoproducts_of_preservesCokernels`：
preservesBinaryCoproducts_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), Prese
rvesColimit (parallelPair f 0) F] : PreservesColimitsOfShape…
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_sub`：map_sub {X Y : C} {f g : X ⟶ Y} : F.map 
(f - g) = F.map f - F.map g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A functor between preadditive categories preserves the coequalizer of two
morphisms if it preserves all cokernels.
-/
lemma preservesCoequalizer_of_preservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) :
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

/-- A functor between preadditive categories preserves all coequalizers if it preserves all
cokernels. -/
/-
**CategoryTheory.Functor.preservesCoequalizers_of_preservesCokernels** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesCoequalizers_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), Pre
servesColimit (parallelPair f 0) F] : PreservesColimitsOfShape WalkingParallelPa
ir F where preservesColimit {K}
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesCoequalizer_of_preservesCokernels`：prese
rvesCoequalizer_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), PreservesColimi
t (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) : Prese…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
A functor between preadditive categories preserves all coequalizers if it preser
ves all
cokernels.
-/
lemma preservesCoequalizers_of_preservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape WalkingParallelPair F where
  preservesColimit {K} := by
    let := preservesCoequalizer_of_preservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm

/-- A functor between preadditive categories which preserves cokernels preserves all finite
colimits. -/
/-
**CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesFiniteColimits_of_preservesCokernels [HasFiniteCoproducts C] [Has
Coequalizers C] [HasZeroObject C] [HasZeroObject D] [forall {X Y} (f : X ⟶ Y), P
reservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F
参数：f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesCoequalizers_of_preservesCokernels`：pres
ervesCoequalizers_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), PreservesColi
mit (parallelPair f 0) F] : PreservesColimitsOfShape Wal…
· 使用引理 `CategoryTheory.Functor.preservesInitialObject_of_preservesZeroMorphisms`
：preservesInitialObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] : P
reservesColimit (Functor.empty.{0} C) F
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_pempty_of_preservesInitia
l`：preservesColimitsOfShape_pempty_of_preservesInitial [PreservesColimit (Functo
r.empty.{0} C) G] : PreservesColimitsOfShape (Discrete PEmpty.{…
· 使用定理 `CategoryTheory.PreservesFiniteCoproducts.of_preserves_binary_and_initial
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1
 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Functor.preservesBinaryCoproducts_of_preservesCokernels`：
preservesBinaryCoproducts_of_preservesCokernels [forall {X Y} (f : X ⟶ Y), Prese
rvesColimit (parallelPair f 0) F] : PreservesColimitsOfShape…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_preservesCoequalizers_a
nd_finiteCoproducts`：preservesFiniteColimits_of_preservesCoequalizers_and_finite
Coproducts [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D) [PreservesCol
i…

--- 原说明 ---
A functor between preadditive categories which preserves cokernels preserves all
 finite
colimits.
-/
lemma preservesFiniteColimits_of_preservesCokernels [HasFiniteCoproducts C] [HasCoequalizers C]
    [HasZeroObject C] [HasZeroObject D]
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F := by
  let := preservesCoequalizers_of_preservesCokernels F
  let := preservesInitialObject_of_preservesZeroMorphisms F
  let := preservesColimitsOfShape_pempty_of_preservesInitial F
  let : PreservesFiniteCoproducts F :=
    ⟨fun _ ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial F _⟩
  exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts F

end FiniteColimits

end Functor

end CategoryTheory

