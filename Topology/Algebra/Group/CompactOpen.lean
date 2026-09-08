/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The compact-open topology on continuous monoid morphisms.
-/

@[expose] public section

open Function Topology
open scoped Pointwise

variable (F A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [IsTopologicalGroup E]

namespace ContinuousMonoidHom

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

@[to_additive]
/-
**ContinuousMonoidHom.isInducing_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMonoidHom`。
形式化陈述：isInducing_toContinuousMap : IsInducing (toContinuousMap : ContinuousMonoi
dHom A B -> C(A, B))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInducing_toContinuousMap :
    IsInducing (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) := ⟨rfl⟩

@[to_additive]
/-
**ContinuousMonoidHom.isEmbedding_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMonoidHom`。
形式化陈述：isEmbedding_toContinuousMap : IsEmbedding (toContinuousMap : ContinuousMon
oidHom A B -> C(A, B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `ContinuousMonoidHom.toContinuousMap_injective`：toContinuousMap_injective
 : Injective (toContinuousMap : _ -> C(A, B))
-/
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨isInducing_toContinuousMap A B, toContinuousMap_injective⟩

@[to_additive]
/-
**ContinuousMonoidHom.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousMonoidHom`。
形式化陈述：instContinuousEvalConst : ContinuousEvalConst (ContinuousMonoidHom A B) A 
B
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEvalConst.of_continuous_forget`：ContinuousEvalConst.of_continu
ous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F'] {f : F' -> F} (hc
 : Continuous f) (hf : forall …
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
-/
instance instContinuousEvalConst : ContinuousEvalConst (ContinuousMonoidHom A B) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
/-
**ContinuousMonoidHom.instContinuousEval** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMo
noidHom`。
形式化陈述：instContinuousEval [LocallyCompactPair A B] : ContinuousEval (ContinuousMo
noidHom A B) A B
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEval.of_continuous_forget`：ContinuousEval.of_continuous_forget
 {F' : Type*} [FunLike F' X Y] [TopologicalSpace F'] {f : F' -> F} (hc : Continu
ous f) (hf : forall g, ⇑(…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
-/
instance instContinuousEval [LocallyCompactPair A B] :
    ContinuousEval (ContinuousMonoidHom A B) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
/-
**ContinuousMonoidHom.range_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMonoidHom`。
形式化陈述：range_toContinuousMap : Set.range (toContinuousMap : ContinuousMonoidHom A
 B -> C(A, B)) = {f : C(A, B) | f 1 = 1 ∧ forall x y, f (x * y) = f x * f y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
lemma range_toContinuousMap :
    Set.range (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) =
      {f : C(A, B) | f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f ↦ ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]
/-
**ContinuousMonoidHom.isClosedEmbedding_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMonoidHom`。
形式化陈述：isClosedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] : IsClosed
Embedding (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) where toIsEmbed
ding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.isEmbedding_toContinuousMap`：isEmbedding_toContinuou
sMap : IsEmbedding (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ContinuousMonoidHom.range_toContinuousMap`：range_toContinuousMap : Set.r
ange (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) = {f : C(A, B) | f 1
 = 1 ∧ forall x y, f (x * y) = …
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
-/
theorem isClosedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    IsClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) where
  toIsEmbedding := isEmbedding_toContinuousMap A B
  isClosed_range := by
    simp only [range_toContinuousMap, Set.ofPred_and, Set.ofPred_forall]
    refine .inter (isClosed_singleton.preimage (continuous_eval_const 1)) <|
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (continuous_eval_const (x * y)) <|
      .mul (continuous_eval_const x) (continuous_eval_const y)

variable {A B C D E}

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (isEmbedding_toContinuousMap A B).t2Space

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := isInducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prodMap hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
/-
**ContinuousMonoidHom.continuous_of_continuous_uncurry** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMonoidHom`。
形式化陈述：continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A] (f : A -
> ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) 
: Continuous f
参数：f : A -> ContinuousMonoidHom B C；h : Continuous (Function.uncurry fun x y => 
f x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
-/
theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A → ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (isInducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]
/-
**ContinuousMonoidHom.continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMonoi
dHom`。
形式化陈述：continuous_comp [LocallyCompactSpace B] : Continuous fun f : ContinuousMon
oidHom A B × ContinuousMonoidHom B C => f.2.comp f.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_comp'`：continuous_comp' : Continuous fun x : C(
X, Y) × C(Y, Z) => x.2.comp x.1
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用引理 `Topology.IsInducing.prodMap`：Topology.IsInducing.prodMap {f : X -> Y} {g
 : Z -> W} (hf : IsInducing f) (hg : IsInducing g) : IsInducing (Prod.map f g)
-/
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((isInducing_toContinuousMap A B).prodMap (isInducing_toContinuousMap B C)).continuous

@[to_additive]
/-
**ContinuousMonoidHom.continuous_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MonoidHom`。
形式化陈述：continuous_comp_left (f : ContinuousMonoidHom A B) : Continuous fun g : Co
ntinuousMonoidHom B C => g.comp f
参数：f : ContinuousMonoidHom A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_precomp.comp (isInducing_toContinuousMap B C).continuous

@[to_additive]
/-
**ContinuousMonoidHom.continuous_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMonoidHom`。
形式化陈述：continuous_comp_right (f : ContinuousMonoidHom B C) : Continuous fun g : C
ontinuousMonoidHom A B => f.comp g
参数：f : ContinuousMonoidHom B C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `ContinuousMonoidHom.isInducing_toContinuousMap`：isInducing_toContinuousM
ap : IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B))
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
  (isInducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_postcomp.comp (isInducing_toContinuousMap A B).continuous

variable (E) in
/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive /-- `ContinuousAddMonoidHom _ f` is a functor. -/]
/-
**ContinuousMonoidHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：compLeft (f : ContinuousMonoidHom A B) : ContinuousMonoidHom (ContinuousMo
noidHom B E) (ContinuousMonoidHom A E) where toFun g
参数：f : ContinuousMonoidHom A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMonoidHom _ f` is a functor.
-/
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

variable (A) in
/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive /-- `ContinuousAddMonoidHom f _` is a functor. -/]
/-
**ContinuousMonoidHom.compRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGro
up B] (f : ContinuousMonoidHom B E) : ContinuousMonoidHom (ContinuousMonoidHom A
 B) (ContinuousMonoidHom A E) where toFun g
参数：f : ContinuousMonoidHom B E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMonoidHom f _` is a functor.
-/
def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

section DiscreteTopology
variable [DiscreteTopology A] [ContinuousMul B] [T2Space B]

@[to_additive]
/-
**ContinuousMonoidHom.isClosedEmbedding_coe** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMonoidHom`。
形式化陈述：isClosedEmbedding_coe : IsClosedEmbedding ((⇑) : (A ->ₜ* B) -> A -> B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用引理 `IsHomeomorph.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbedding f
· 使用引理 `ContinuousMap.isHomeomorph_coe`：isHomeomorph_coe : IsHomeomorph ((⇑) : C
(X, Y) -> X -> Y)
· 使用定理 `ContinuousMonoidHom.isClosedEmbedding_toContinuousMap`：isClosedEmbedding
_toContinuousMap [ContinuousMul B] [T2Space B] : IsClosedEmbedding (toContinuous
Map : ContinuousMonoidHom A B -> C(A, B)) w…
-/
lemma isClosedEmbedding_coe : IsClosedEmbedding ((⇑) : (A →ₜ* B) → A → B) :=
  ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp <| isClosedEmbedding_toContinuousMap ..

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace B] : CompactSpace (A →ₜ* B) :=
  ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

end DiscreteTopology

section LocallyCompact

variable {X Y : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
  [UniformSpace Y] [CommGroup Y] [IsUniformGroup Y] [T0Space Y] [CompactSpace Y]

@[to_additive]
/-
**ContinuousMonoidHom.locallyCompactSpace_of_equicontinuousAt** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：locallyCompactSpace_of_equicontinuousAt (U : Set X) (V : Set Y) (hU : IsCo
mpact U) (hV : V in nhds (1 : Y)) (h : EquicontinuousAt (fun f : {f : X ->* Y | 
Set.MapsTo f U V} => (f : X -> Y)) 1) : LocallyCompactSpace (ContinuousMonoidHom
 X Y)
参数：U : Set X；V : Set Y；hU : IsCompact U；hV : V in nhds (1 : Y)；h : Equicontinuou
sAt (fun f : {f : X ->* Y | Set.MapsTo f U V} => (f : X -> Y)) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `equicontinuous_of_equicontinuousAt_one`：equicontinuous_of_equicontinuous
At_one {ι G M hom : Type*} [TopologicalSpace G] [UniformSpace M] [Group G] [Grou
p M] [IsTopologicalGroup G] …
· 使用定理 `local_compact_nhds`：local_compact_nhds [LocallyCompactSpace X] {x : X} {
n : Set X} (h : n in 𝓝 x) : exists s in 𝓝 x, s subseteq n ∧ IsCompact s
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Equicontinuous.comp`：Equicontinuous.comp {F : ι -> X -> α} (h : Equicont
inuous F) (u : κ -> ι) : Equicontinuous (F ∘ u)
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equicontinuous.continuous`：Equicontinuous.continuous {F : ι -> X -> α} (
h : Equicontinuous F) (i : ι) : Continuous (F i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuous_iff_range`：equicontinuous_iff_range {F : ι -> X -> α} : E
quicontinuous F ↔ Equicontinuous ((↑) : range F -> X -> α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_set_pi`：isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (
hs : forall a in i, IsClosed (s a)) : IsClosed (pi i s)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `instT1SpaceOfT0SpaceOfR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [T0Space X] [R0Space X], T1Space X
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `MonoidHom.isClosed_range_coe`：MonoidHom.isClosed_range_coe : IsClosed (S
et.range ((↑) : (M₁ ->* M₂) -> M₁ -> M₂))
（共 45 条，此处仅展示前 30 条）
-/
theorem locallyCompactSpace_of_equicontinuousAt (U : Set X) (V : Set Y)
    (hU : IsCompact U) (hV : V ∈ nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U V} ↦ (f : X → Y)) 1) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  obtain ⟨W, hWo, hWV, hWc⟩ := local_compact_nhds hV
  let S1 : Set (X →* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) :=
    h.comp (Subtype.map _root_.id fun f hf ↦ hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ W) ∩ Set.range ((↑) : (X →* Y) → (X → Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f ↦ ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ ↦ hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  have hS2 : (interior S2).Nonempty := by
    let T : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U (interior W)}
    have h1 : T.Nonempty := ⟨1, fun _ _ ↦ mem_interior_iff_mem_nhds.mpr hWo⟩
    have h2 : T ⊆ S2 := fun f hf ↦ hf.mono_right interior_subset
    have h3 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hU isOpen_interior)
    exact h1.mono (interior_maximal h2 h3)
  exact TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    ⟨⟨S2, (isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)⟩, hS2⟩

variable [LocallyCompactSpace X]

@[to_additive]
/-
**ContinuousMonoidHom.locallyCompactSpace_of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMonoidHom`。
形式化陈述：locallyCompactSpace_of_hasBasis (V : Nat -> Set Y) (hV : forall {n x}, x i
n V n -> x * x in V n -> x in V (n + 1)) (hVo : Filter.HasBasis (nhds 1) (fun _ 
=> True) V) : LocallyCompactSpace (ContinuousMonoidHom X Y)
参数：V : Nat -> Set Y；hV : forall {n x}, x in V n -> x * x in V n -> x in V (n + 1
)；hVo : Filter.HasBasis (nhds 1) (fun _ => True) V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `exists_closed_nhds_one_inv_eq_mul_subset`：exists_closed_nhds_one_inv_eq_
mul_subset {U : Set G} (hU : U in 𝓝 1) : exists V in 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧
 V * V subseteq U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ContinuousMonoidHom.locallyCompactSpace_of_equicontinuousAt`：locallyComp
actSpace_of_equicontinuousAt (U : Set X) (V : Set Y) (hU : IsCompact U) (hV : V 
in nhds (1 : Y)) (h : EquicontinuousAt (fun f : {…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.equicontinuousAt_iff_right`：Filter.HasBasis.equicontinuo
usAt_iff_right {p : κ -> Prop} {s : κ -> Set (α × α)} {F : ι -> X -> α} {x₀ : X}
 (hα : (𝓤 α).HasBasis p s) : Equ…
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_one`：Filter.HasBasis.uniformity_of_nh
ds_one {ι} {p : ι -> Prop} {U : ι -> Set α} (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 
α).HasBasis p fun i => { x :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem locallyCompactSpace_of_hasBasis (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : ∀ f : X →* Y, Set.MapsTo f (U 0) (V 0) → ∀ n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  apply locallyCompactSpace_of_equicontinuousAt (U 0) (V 0) hU0c (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ ?_⟩
  rw [Set.mem_ofPred_eq, map_one, div_one]
  exact hU4 f hf n hx

end LocallyCompact

end ContinuousMonoidHom

