/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f g : E → F} {f' g' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/


variable (x)

/-
**HasFDerivAtFilter.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[𝕜] G} {L' : Filter (F × F)
} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L) (hL : Tendsto
 (Prod.map f f) L L') : HasFDerivAtFilter (g ∘ f) (g' ∘L f') L
参数：F × F；hg : HasFDerivAtFilter g g' L'；hf : HasFDerivAtFilter f f' L；hL : Tends
to (Prod.map f f) L L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleOTVS.add`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Asymptotics.IsLittleOTVS.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {
𝕜 : Type u_3} {E : Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]  
 [inst_1 : AddCommGroup E] …
· 使用定理 `HasFDerivAtFilter.isLittleOTVS`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `HasFDerivAtFilter.isBigOTVS_sub`：HasFDerivAtFilter.isBigOTVS_sub (hf : H
asFDerivAtFilter f f' L) : (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => p.1 - p.2
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
-/
theorem HasFDerivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter (F × F)}
    (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L)
    (hL : Tendsto (Prod.map f f) L L') :
    HasFDerivAtFilter (g ∘ f) (g' ∘L f') L := by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
  refine .of_isLittleOTVS <| calc
    (fun p ↦ (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p ↦ (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p ↦ g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p ↦ f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p ↦ g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isLittleOTVS

/-- The chain rule for derivatives in the sense of strict differentiability. -/
@[fun_prop]
/-
**HasStrictFDerivAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f : E → F} {f' : E →L[𝕜] F} (x : E)
 {g : F → G}   {g' : F →L[𝕜] G},   HasStrictFDerivAt g g' (f x) → HasStrictFDeri
vAt f f' x → HasStrictFDerivAt (fun x => g (f x)) (g' ∘SL f') x
参数：x : E；f x；fun x => g (f x)；g' ∘SL f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `Filter.Tendsto.prodMap_nhds`：Filter.Tendsto.prodMap_nhds {x : X} {y : Y}
 {z : Z} {w : W} {f : X -> Y} {g : Z -> W} (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Te
ndsto g (𝓝 z) (𝓝 …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasStrictFDerivAt.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The chain rule for derivatives in the sense of strict differentiability.
-/
protected theorem HasStrictFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasStrictFDerivAt g g' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => g (f x)) (g'.comp f') x :=
  HasFDerivAtFilter.comp hg hf <| hf.continuousAt.tendsto.prodMap_nhds hf.continuousAt.tendsto

@[fun_prop]
/-
**HasFDerivWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F} (hg : Ha
sFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f 
s t) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x
参数：hg : HasFDerivWithinAt g g' t (f x)；hf : HasFDerivWithinAt f f' s x；hst : Map
sTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasFDerivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp hg hf <| .prodMap (hf.continuousWithinAt.tendsto_nhdsWithin hst) <|
    tendsto_pure_pure ..

@[fun_prop]
/-
**HasFDerivAt.comp_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_hasFDerivWithinAt {g : F -> G} {g' : F ->L[𝕜] G} (hg : Ha
sFDerivAt g g' (f x)) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (g ∘
 f) (g'.comp f') s x
参数：hg : HasFDerivAt g g' (f x)；hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem HasFDerivAt.comp_hasFDerivWithinAt {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.hasFDerivWithinAt.comp x hf (mapsTo_univ _ _)

@[fun_prop]
/-
**HasFDerivWithinAt.comp_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_of_tendsto {g : F -> G} {g' : F ->L[𝕜] G} {t : Set 
F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst 
: Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x
参数：hg : HasFDerivWithinAt g g' t (f x)；hf : HasFDerivWithinAt f f' s x；hst : Ten
dsto f (𝓝[s] x) (𝓝[t] f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasFDerivWithinAt.comp_of_tendsto {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp hg hf <| hst.prodMap <| tendsto_pure_pure ..
/-
**HasFDerivWithinAt.comp_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasFDerivAt {g : F -> G} {g' : F ->L[𝕜] G} {t : Set
 F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivAt f f' x) (ht : forall
ᶠ x' in 𝓝 x, f x' in t) : HasFDerivAt (g ∘ f) (g' ∘L f') x
参数：hg : HasFDerivWithinAt g g' t (f x)；hf : HasFDerivAt f f' x；ht : forallᶠ x' i
n 𝓝 x, f x' in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasFDerivWithinAt.comp_hasFDerivAt {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivAt f f' x)
    (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) : HasFDerivAt (g ∘ f) (g' ∘L f') x :=
  HasFDerivAtFilter.comp hg hf <| .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩) <|
    tendsto_pure_pure ..
/-
**HasFDerivWithinAt.comp_hasFDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasFDerivAt_of_eq {g : F -> G} {g' : F ->L[𝕜] G} {t
 : Set F} {y : F} (hg : HasFDerivWithinAt g g' t y) (hf : HasFDerivAt f f' x) (h
t : forallᶠ x' in 𝓝 x, f x' in t) (hy : y = f x) : HasFDerivAt (g ∘ f) (g' ∘L f'
) x
参数：hg : HasFDerivWithinAt g g' t y；hf : HasFDerivAt f f' x；ht : forallᶠ x' in 𝓝 
x, f x' in t；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.comp_hasFDerivAt`：HasFDerivWithinAt.comp_hasFDerivAt {
g : F -> G} {g' : F ->L[𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) 
(hf : HasFDerivAt f f' x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasFDerivWithinAt.comp_hasFDerivAt_of_eq {g : F → G} {g' : F →L[𝕜] G} {t : Set F} {y : F}
    (hg : HasFDerivWithinAt g g' t y) (hf : HasFDerivAt f f' x)
    (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) (hy : y = f x) : HasFDerivAt (g ∘ f) (g' ∘L f') x := by
  subst y; exact hg.comp_hasFDerivAt x hf ht

/-- The chain rule. -/
@[fun_prop]
/-
**HasFDerivAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f 
x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x
参数：hg : HasFDerivAt g g' (f x)；hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))

--- 原说明 ---
The chain rule.
-/
theorem HasFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFDerivAt g g' (f x))
    (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x :=
  HasFDerivAtFilter.comp hg hf <| hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure ..

@[fun_prop]
/-
**DifferentiableWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.comp {g : F -> G} {t : Set F} (hg : DifferentiableW
ithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) : 
DifferentiableWithinAt 𝕜 (g ∘ f) s x
参数：hg : DifferentiableWithinAt 𝕜 g t (f x)；hf : DifferentiableWithinAt 𝕜 f s x；h
 : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
    (h : MapsTo f s t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.comp' {g : F -> G} {t : Set F} (hg : Differentiable
WithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWith
inAt 𝕜 (g ∘ f) (s inter f ⁻¹' t) x
参数：hg : DifferentiableWithinAt 𝕜 g t (f x)；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

@[fun_prop]
/-
**DifferentiableAt.fun_comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fun_comp' {f : E -> F} {g : F -> G} (hg : DifferentiableA
t 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun x => g (f x
)) x
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.fun_comp' {f : E → F} {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun x ↦ g (f x)) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
/-
**DifferentiableAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf :
 DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
/-
**DifferentiableAt.comp_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.comp_differentiableWithinAt {g : F -> G} (hg : Differenti
ableAt 𝕜 g (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt
 𝕜 (g ∘ f) s x
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem DifferentiableAt.comp_differentiableWithinAt {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
@[to_fun fderivWithin_fun_comp]
/-
**fderivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp {g : F -> G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 
g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : Uniqu
eDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).c
omp (fderivWithin 𝕜 f s x)
参数：hg : DifferentiableWithinAt 𝕜 g t (f x)；hf : DifferentiableWithinAt 𝕜 f s x；h
 : MapsTo f s t；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs

@[to_fun fderivWithin_fun_comp_of_eq]
/-
**fderivWithin_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_of_eq {g : F -> G} {t : Set F} {y : F} (hg : Differentia
bleWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (h
xs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) : fderivWithin 𝕜 (g ∘ f) s x = (fd
erivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x)
参数：hg : DifferentiableWithinAt 𝕜 g t y；hf : DifferentiableWithinAt 𝕜 f s x；h : M
apsTo f s t；hxs : UniqueDiffWithinAt 𝕜 s x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_comp`：fderivWithin_comp {g : F -> G} {t : Set F} (hg : Diff
erentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsT
o f s t…
-/
theorem fderivWithin_comp_of_eq {g : F → G} {t : Set F} {y : F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) := by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

@[deprecated (since := "2026-05-18")] alias fderivWithin_comp' := fderivWithin_fun_comp
@[deprecated (since := "2026-05-18")] alias fderivWithin_comp_of_eq' := fderivWithin_fun_comp_of_eq

/-- A version of `fderivWithin_comp` that is useful to rewrite the composition of two derivatives
  into a single derivative. This version always applies, but creates a new side-goal `f x = y`. -/
/-
**fderivWithin_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fderivWithin {g : F -> G} {f : E -> F} {x : E} {y : F} {s : S
et E} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWith
inAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y)
 (v : E) : fderivWithin 𝕜 g t y (fderivWithin 𝕜 f s x v) = fderivWithin 𝕜 (g ∘ f
) s x v
参数：hg : DifferentiableWithinAt 𝕜 g t y；hf : DifferentiableWithinAt 𝕜 f s x；h : M
apsTo f s t；hxs : UniqueDiffWithinAt 𝕜 s x；hy : f x = y；v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_comp`：fderivWithin_comp {g : F -> G} {t : Set F} (hg : Diff
erentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsT
o f s t…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)

--- 原说明 ---
A version of `fderivWithin_comp` that is useful to rewrite the composition of tw
o derivatives
  into a single derivative. This version always applies, but creates a new side-
goal `f x = y`.
-/
theorem fderivWithin_fderivWithin {g : F → G} {f : E → F} {x : E} {y : F} {s : Set E} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) (v : E) :
    fderivWithin 𝕜 g t y (fderivWithin 𝕜 f s x v) = fderivWithin 𝕜 (g ∘ f) s x v := by
  subst y
  rw [fderivWithin_comp x hg hf h hxs, comp_apply]

/-- Ternary version of `fderivWithin_comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
/-
**fderivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp {g : F -> G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 
g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : Uniqu
eDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).c
omp (fderivWithin 𝕜 f s x)
参数：hg : DifferentiableWithinAt 𝕜 g t (f x)；hf : DifferentiableWithinAt 𝕜 f s x；h
 : MapsTo f s t；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
Ternary version of `fderivWithin_comp`, with equality assumptions of basepoints 
added, in
  order to apply more easily as a rewrite from right-to-left.
-/
theorem fderivWithin_comp₃ {g' : G → G'} {g : F → G} {t : Set F} {u : Set G} {y : F} {y' : G}
    (hg' : DifferentiableWithinAt 𝕜 g' u y') (hg : DifferentiableWithinAt 𝕜 g t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (h2g : MapsTo g t u) (h2f : MapsTo f s t) (h3g : g y = y')
    (h3f : f x = y) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g' ∘ g ∘ f) s x =
      (fderivWithin 𝕜 g' u y').comp ((fderivWithin 𝕜 g t y).comp (fderivWithin 𝕜 f s x)) := by
  subst h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs

@[to_fun fderiv_fun_comp]
/-
**fderiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Different
iableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x)
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
@[deprecated (since := "2026-05-18")] alias fderiv_comp' := fderiv_fun_comp
/-
**fderiv_comp_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_fderivWithin {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (h
f : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWit
hin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x)
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : DifferentiableWithinAt 𝕜 f s x；hxs : Uni
queDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderiv_comp_fderivWithin {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
/-
**DifferentiableOn.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.fun_comp {g : F -> G} {t : Set F} (hg : DifferentiableOn 
𝕜 g t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (f
un x => g (f x)) s
参数：hg : DifferentiableOn 𝕜 g t；hf : DifferentiableOn 𝕜 f s；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
-/
theorem DifferentiableOn.fun_comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) :
    DifferentiableOn 𝕜 (fun x ↦ g (f x)) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
/-
**DifferentiableOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.comp {g : F -> G} {t : Set F} (hg : DifferentiableOn 𝕜 g 
t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f
) s
参数：hg : DifferentiableOn 𝕜 g t；hf : DifferentiableOn 𝕜 f s；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
-/
theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
/-
**Differentiable.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.fun_comp {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Diffe
rentiable 𝕜 f) : Differentiable 𝕜 (fun x => g (f x))
参数：hg : Differentiable 𝕜 g；hf : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
-/
theorem Differentiable.fun_comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun x ↦ g (f x)) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
/-
**Differentiable.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Different
iable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
参数：hg : Differentiable 𝕜 g；hf : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
-/
theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (g ∘ f) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
/-
**Differentiable.comp_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp_differentiableOn {g : F -> G} (hg : Differentiable 𝕜 g
) (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s
参数：hg : Differentiable 𝕜 g；hf : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.comp`：DifferentiableOn.comp {g : F -> G} {t : Set F} (h
g : DifferentiableOn 𝕜 g t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : 
Differentia…
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem Differentiable.comp_differentiableOn {g : F → G} (hg : Differentiable 𝕜 g)
    (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  hg.differentiableOn.comp hf (mapsTo_univ _ _)


@[fun_prop]
/-
**Differentiable.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : E → E}, Differentiabl
e 𝕜 f → ∀ (n : ℕ), Differentiable 𝕜 f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
-/
protected theorem Differentiable.iterate {f : E → E} (hf : Differentiable 𝕜 f) (n : ℕ) :
    Differentiable 𝕜 f^[n] :=
  Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf

@[fun_prop]
/-
**DifferentiableOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {s : Set E} {f : E → E},  
 DifferentiableOn 𝕜 f s → Set.MapsTo f s s → ∀ (n : ℕ), DifferentiableOn 𝕜 f^[n]
 s
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `DifferentiableOn.comp`：DifferentiableOn.comp {g : F -> G} {t : Set F} (h
g : DifferentiableOn 𝕜 g t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : 
Differentia…
-/
protected theorem DifferentiableOn.iterate {f : E → E} (hf : DifferentiableOn 𝕜 f s)
    (hs : MapsTo f s s) (n : ℕ) : DifferentiableOn 𝕜 f^[n] s :=
  Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs

variable {x}
/-
**HasFDerivAtFilter.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAtFilter`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {L : Filter (E × E)} {f : 
E → E} {f' : E →L[𝕜] E},   HasFDerivAtFilter f f' L → Filter.Tendsto (Prod.map f
 f) L L → ∀ (n : ℕ), HasFDerivAtFilter f^[n] (f' ^ n) L
参数：E × E；Prod.map f f；n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFDerivAtFilter_id`：hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDe
rivAtFilter id (.id 𝕜 E) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
-/
protected theorem HasFDerivAtFilter.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : ℕ) :
    HasFDerivAtFilter f^[n] (f' ^ n) L := by
  induction n with
  | zero => exact hasFDerivAtFilter_id L
  | succ n ihn =>
    rw [Function.iterate_succ, pow_succ]
    exact ihn.comp hf hL

@[fun_prop]
/-
**HasFDerivAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {f : E → E} {f' : 
E →L[𝕜] E},   HasFDerivAt f f' x → f x = x → ∀ (n : ℕ), HasFDerivAt f^[n] (f' ^ 
n) x
参数：n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {L : Filter …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
protected theorem HasFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousAt.tendsto.prodMap (tendsto_pure_pure f x)

@[fun_prop]
/-
**HasFDerivWithinAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {s : Set E} {f : E
 → E} {f' : E →L[𝕜] E},   HasFDerivWithinAt f f' s x → f x = x → Set.MapsTo f s 
s → ∀ (n : ℕ), HasFDerivWithinAt f^[n] (f' ^ n) s x
参数：n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {L : Filter …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
protected theorem HasFDerivWithinAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivWithinAt f f' s x) (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) :
    HasFDerivWithinAt f^[n] (f' ^ n) s x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousWithinAt.tendsto_nhdsWithin hs |>.prodMap (tendsto_pure_pure f x)

@[fun_prop]
/-
**HasStrictFDerivAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {f : E → E} {f' : 
E →L[𝕜] E},   HasStrictFDerivAt f f' x → f x = x → ∀ (n : ℕ), HasStrictFDerivAt 
f^[n] (f' ^ n) x
参数：n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {L : Filter …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousAt.prodMap'`：ContinuousAt.prodMap' {f : X -> Z} {g : Y -> W} {
x : X} {y : Y} (hf : ContinuousAt f x) (hg : ContinuousAt g y) : ContinuousAt (P
rod.map f g…
· 使用定理 `HasStrictFDerivAt.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
protected theorem HasStrictFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasStrictFDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx, ContinuousAt] using hf.continuousAt.prodMap' hf.continuousAt

@[fun_prop]
/-
**DifferentiableAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {f : E → E},   Dif
ferentiableAt 𝕜 f x → f x = x → ∀ (n : ℕ), DifferentiableAt 𝕜 f^[n] x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x 
: E} {f :…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
protected theorem DifferentiableAt.iterate {f : E → E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
    (n : ℕ) : DifferentiableAt 𝕜 f^[n] x :=
  (hf.hasFDerivAt.iterate hx n).differentiableAt

@[fun_prop]
/-
**DifferentiableWithinAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWithin
At`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {s : Set E} {f : E
 → E},   DifferentiableWithinAt 𝕜 f s x → f x = x → Set.MapsTo f s s → ∀ (n : ℕ)
, DifferentiableWithinAt 𝕜 f^[n] s x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {x : E} {s :…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
protected theorem DifferentiableWithinAt.iterate {f : E → E} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : DifferentiableWithinAt 𝕜 f^[n] s x :=
  (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt

end Composition

end

