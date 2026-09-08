/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Inverse function theorem, the "easy half"

In this file we prove several versions of the following theorem.
Consider three functions `f : F → G`, `g : E → F`, and `h : E → G`,
together with "candidate derivatives" `f' : F →L[𝕜] G`, `g' : E →L[𝕜] F`, and `h' : E →L[𝕜] G`.
Suppose that

- `f ∘ g = h` in a neighborhood of `a`;
- `h` has derivative `h'` at `a`;
- `f` has derivative `f'` at `g a`;
- `g` is continuous at `a`;
- either `f'` has a right inverse `f'⁻¹` and `g' = f'⁻¹ ∘ h'`,
  or `f'` is a topological embedding and `h' = f' ∘ g'`.

Then `g` has derivative `g'` at `a`.
We prove these theorems for different differentiability predicates,
then specialize it to the cases when `f'` is a linear equivalence and/or `h = id`.
-/

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

public section

section OfComp

variable {g : E → F} {f : F → G} {h : E → G}
  {g' : E →L[𝕜] F} {f' : F →L[𝕜] G} {h' : E →L[𝕜] G} {f'symm : G →L[𝕜] F}
  {lE : Filter (E × E)} {lF : Filter (F × F)}
  {a : E} {s : Set E} {t : Set F}

/-
**HasFDerivAtFilter.of_comp_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem HasFDerivAtFilter.of_comp_aux (hf_emb : Topology.IsEmbedding f')
    (htendsto : Tendsto (Prod.map g g) lE lF)
    (hh : HasFDerivAtFilter h h' lE)
    (hf : HasFDerivAtFilter f f' lF)
    (hcomp : Prod.map (f ∘ g) (f ∘ g) =ᶠ[lE] Prod.map h h)
    (ho : (fun (x, y) ↦ g x - g y - g' (x - y)) =O[𝕜; lE]
      (fun (x, y) ↦ f' (g x - g y) - h' (x - y))) :
    HasFDerivAtFilter g g' lE := by
  refine .of_isLittleOTVS <| ho.trans_isLittleOTVS <| .triangle (.symm ?_) hh.isLittleOTVS
  refine (hf.isLittleOTVS.comp_tendsto htendsto).congr' ?_ .rfl |>.trans_isBigOTVS ?_
  · refine hcomp.mono ?_
    simp +contextual
  · refine hf.isThetaTVS_sub hf_emb.isInducing |>.symm.isBigOTVS.comp_tendsto htendsto |>.trans ?_
    refine hh.isBigOTVS_sub.congr' (hcomp.mono ?_) .rfl
    simp +contextual

/-!
### Left inverse

In this section, we prove that `g` has derivative `f'⁻¹ ∘ h'`
whenever `h = f ∘ g` has derivative `h'` and `f'⁻¹` is a left inverse to `f'`.
-/

/-
**HasFDerivAtFilter.of_comp_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.of_comp_of_leftInverse (hg : Tendsto (Prod.map g g) lE l
F) (hf : HasFDerivAtFilter f f' lF) (hh : HasFDerivAtFilter h h' lE) (hcomp : (P
rod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h) (hf'symm : Function.LeftInverse f'
symm f') : HasFDerivAtFilter g (f'symm ∘L h') lE
参数：hg : Tendsto (Prod.map g g) lE lF；hf : HasFDerivAtFilter f f' lF；hh : HasFDer
ivAtFilter h h' lE；hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h；hf'sym
m : Function.LeftInverse f'symm f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.OfCompLeft.0.HasFDerivAtFilter
.of_comp_aux`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [ins
t : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.of_leftInverse`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {g : Y → X}, 
  Function.LeftInverse f …
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Asymptotics.IsBigOTVS.congr_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `ContinuousLinearMap.isBigOTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E :
 Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddComm
Group E] [inst_2 : Topol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Left inverse

In this section, we prove that `g` has derivative `f'⁻¹ ∘ h'`
whenever `h = f ∘ g` has derivative `h'` and `f'⁻¹` is a left inverse to `f'`.
-/
theorem HasFDerivAtFilter.of_comp_of_leftInverse
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hh : HasFDerivAtFilter h h' lE) (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAtFilter g (f'symm ∘L h') lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  · exact Topology.IsEmbedding.of_leftInverse hf'symm (map_continuous _) (map_continuous _)
  · refine f'symm.isBigOTVS_comp.congr_left ?_
    simp [hf'symm _]
/-
**HasFDerivWithinAt.of_comp_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_comp_of_leftInverse (hst : Tendsto g (𝓝[s] a) (𝓝[t] (
g a))) (hf : HasFDerivWithinAt f f' t (g a)) (hh : HasFDerivWithinAt h h' s a) (
hcomp : f ∘ g =ᶠ[𝓝[s] a] h) (hf'symm : Function.LeftInverse f'symm f') (ha : a i
n s) : HasFDerivWithinAt g (f'symm ∘L h') s a
参数：hst : Tendsto g (𝓝[s] a) (𝓝[t] (g a))；hf : HasFDerivWithinAt f f' t (g a)；hh 
: HasFDerivWithinAt h h' s a；hcomp : f ∘ g =ᶠ[𝓝[s] a] h；hf'symm : Function.LeftI
nverse f'symm f'；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_leftInverse`：HasFDerivAtFilter.of_comp_of_l
eftInverse (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hh : HasFDerivAtFilter h h' l…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem HasFDerivWithinAt.of_comp_of_leftInverse
    (hst : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hh : HasFDerivWithinAt h h' s a) (hcomp : f ∘ g =ᶠ[𝓝[s] a] h)
    (hf'symm : Function.LeftInverse f'symm f') (ha : a ∈ s) :
    HasFDerivWithinAt g (f'symm ∘L h') s a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hst.prodMap (by simp)
  · exact hcomp.prodMap (hcomp.self_of_nhdsWithin ha)
/-
**HasFDerivAt.of_comp_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.of_comp_of_leftInverse (hgc : ContinuousAt g a) (hf : HasFDeri
vAt f f' (g a)) (hh : HasFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h) (hf'symm : F
unction.LeftInverse f'symm f') : HasFDerivAt g (f'symm ∘L h') a
参数：hgc : ContinuousAt g a；hf : HasFDerivAt f f' (g a)；hh : HasFDerivAt h h' a；hc
omp : f ∘ g =ᶠ[𝓝 a] h；hf'symm : Function.LeftInverse f'symm f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_leftInverse`：HasFDerivAtFilter.of_comp_of_l
eftInverse (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hh : HasFDerivAtFilter h h' l…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem HasFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hh : HasFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasFDerivAt g (f'symm ∘L h') a := by
  refine HasFDerivAtFilter.of_comp_of_leftInverse ?_ hf hh ?_ hf'symm
  · exact hgc.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds
/-
**HasStrictFDerivAt.of_comp_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.of_comp_of_leftInverse (hgc : ContinuousAt g a) (hf : Ha
sStrictFDerivAt f f' (g a)) (hh : HasStrictFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 
a] h) (hf'symm : Function.LeftInverse f'symm f') : HasStrictFDerivAt g (f'symm ∘
L h') a
参数：hgc : ContinuousAt g a；hf : HasStrictFDerivAt f f' (g a)；hh : HasStrictFDeriv
At h h' a；hcomp : f ∘ g =ᶠ[𝓝 a] h；hf'symm : Function.LeftInverse f'symm f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_leftInverse`：HasFDerivAtFilter.of_comp_of_l
eftInverse (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hh : HasFDerivAtFilter h h' l…
· 使用定理 `Filter.Tendsto.prodMap_nhds`：Filter.Tendsto.prodMap_nhds {x : X} {y : Y}
 {z : Z} {w : W} {f : X -> Y} {g : Z -> W} (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Te
ndsto g (𝓝 z) (𝓝 …
· 使用定理 `Filter.EventuallyEq.prodMap_nhds`：Filter.EventuallyEq.prodMap_nhds {α β 
: Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β} {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) 
(hg : g₁ =ᶠ[𝓝 y] g₂) :…
-/
theorem HasStrictFDerivAt.of_comp_of_leftInverse
    (hgc : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hh : HasStrictFDerivAt h h' a) (hcomp : f ∘ g =ᶠ[𝓝 a] h)
    (hf'symm : Function.LeftInverse f'symm f') :
    HasStrictFDerivAt g (f'symm ∘L h') a :=
  HasFDerivAtFilter.of_comp_of_leftInverse (hgc.prodMap_nhds hgc) hf hh
    (hcomp.prodMap_nhds hcomp) hf'symm


/-!
### Embedding

In this section we show that `g` has derivative `g'`
provided that `h = f ∘ g` has derivative `f' ∘ g'`, where `f'` is a topological embedding.
-/

/-
**HasFDerivAtFilter.of_comp_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.of_comp_of_isEmbedding (hg : Tendsto (Prod.map g g) lE l
F) (hf : HasFDerivAtFilter f f' lF) (hf' : Topology.IsEmbedding f') (hh : HasFDe
rivAtFilter h (f' ∘L g') lE) (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map
 h h) : HasFDerivAtFilter g g' lE
参数：hg : Tendsto (Prod.map g g) lE lF；hf : HasFDerivAtFilter f f' lF；hf' : Topolo
gy.IsEmbedding f'；hh : HasFDerivAtFilter h (f' ∘L g') lE；hcomp : (Prod.map (f ∘ 
g) (f ∘ g)) =ᶠ[lE] Prod.map h h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.OfCompLeft.0.HasFDerivAtFilter
.of_comp_aux`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [ins
t : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 :…
· 使用定理 `Asymptotics.IsBigOTVS.congr_right`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : 
Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommG
roup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsThetaTVS.isBigOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGr
oup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsThetaTVS.symm`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u
_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E
] [inst_2 : Topol…
· 使用定理 `ContinuousLinearMap.isThetaTVS_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Embedding

In this section we show that `g` has derivative `g'`
provided that `h = f ∘ g` has derivative `f' ∘ g'`, where `f'` is a topological 
embedding.
-/
theorem HasFDerivAtFilter.of_comp_of_isEmbedding
    (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF)
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAtFilter h (f' ∘L g') lE)
    (hcomp : (Prod.map (f ∘ g) (f ∘ g)) =ᶠ[lE] Prod.map h h) :
    HasFDerivAtFilter g g' lE := by
  apply of_comp_aux (f := f) (f' := f') <;> try assumption
  refine f'.isThetaTVS_comp hf'.isInducing |>.symm.isBigOTVS.congr_right ?_
  simp
/-
**HasFDerivWithinAt.of_comp_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_comp_of_isEmbedding (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g
 a))) (hf : HasFDerivWithinAt f f' t (g a)) (hf' : Topology.IsEmbedding f') (hh 
: HasFDerivWithinAt h (f' ∘L g') s a) (hcomp : (f ∘ g) =ᶠ[𝓝[s] a] h) (ha : a in 
s) : HasFDerivWithinAt g g' s a
参数：hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))；hf : HasFDerivWithinAt f f' t (g a)；hf' 
: Topology.IsEmbedding f'；hh : HasFDerivWithinAt h (f' ∘L g') s a；hcomp : (f ∘ g
) =ᶠ[𝓝[s] a] h；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_isEmbedding`：HasFDerivAtFilter.of_comp_of_i
sEmbedding (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hf' : Topology.IsEmbedding f'…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem HasFDerivWithinAt.of_comp_of_isEmbedding
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' t (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivWithinAt h (f' ∘L g') s a)
    (hcomp : (f ∘ g) =ᶠ[𝓝[s] a] h) (ha : a ∈ s) :
    HasFDerivWithinAt g g' s a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.prodMap (by simp)
  · exact hcomp.prodMap <| hcomp.self_of_nhdsWithin ha
/-
**HasFDerivAt.of_comp_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.of_comp_of_isEmbedding (hg : ContinuousAt g a) (hf : HasFDeriv
At f f' (g a)) (hf' : Topology.IsEmbedding f') (hh : HasFDerivAt h (f' ∘L g') a)
 (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) : HasFDerivAt g g' a
参数：hg : ContinuousAt g a；hf : HasFDerivAt f f' (g a)；hf' : Topology.IsEmbedding 
f'；hh : HasFDerivAt h (f' ∘L g') a；hcomp : (f ∘ g) =ᶠ[𝓝 a] h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_isEmbedding`：HasFDerivAtFilter.of_comp_of_i
sEmbedding (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hf' : Topology.IsEmbedding f'…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_6} {la : Filter α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Fil
ter β} {fb gb : β…
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem HasFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasFDerivAt g g' a := by
  refine HasFDerivAtFilter.of_comp_of_isEmbedding ?_ hf hf' hh ?_
  · exact hg.tendsto.prodMap (by simp)
  · exact hcomp.prodMap hcomp.self_of_nhds
/-
**HasStrictFDerivAt.of_comp_of_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.of_comp_of_isEmbedding (hg : ContinuousAt g a) (hf : Has
StrictFDerivAt f f' (g a)) (hf' : Topology.IsEmbedding f') (hh : HasStrictFDeriv
At h (f' ∘L g') a) (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) : HasStrictFDerivAt g g' a
参数：hg : ContinuousAt g a；hf : HasStrictFDerivAt f f' (g a)；hf' : Topology.IsEmbe
dding f'；hh : HasStrictFDerivAt h (f' ∘L g') a；hcomp : (f ∘ g) =ᶠ[𝓝 a] h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_comp_of_isEmbedding`：HasFDerivAtFilter.of_comp_of_i
sEmbedding (hg : Tendsto (Prod.map g g) lE lF) (hf : HasFDerivAtFilter f f' lF) 
(hf' : Topology.IsEmbedding f'…
· 使用定理 `ContinuousAt.prodMap`：ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p 
: X × Y} (hf : ContinuousAt f p.fst) (hg : ContinuousAt g p.snd) : ContinuousAt 
(Prod.map …
· 使用定理 `Filter.EventuallyEq.prodMap_nhds`：Filter.EventuallyEq.prodMap_nhds {α β 
: Type*} {f₁ f₂ : X -> α} {g₁ g₂ : Y -> β} {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) 
(hg : g₁ =ᶠ[𝓝 y] g₂) :…
-/
theorem HasStrictFDerivAt.of_comp_of_isEmbedding
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a))
    (hf' : Topology.IsEmbedding f') (hh : HasStrictFDerivAt h (f' ∘L g') a)
    (hcomp : (f ∘ g) =ᶠ[𝓝 a] h) :
    HasStrictFDerivAt g g' a :=
  HasFDerivAtFilter.of_comp_of_isEmbedding (hg.prodMap hg) hf hf' hh (hcomp.prodMap_nhds hcomp)

end OfComp

/-!
### Local left inverse (equivalence)
-/

section LeftInverse

variable {g : E → F} {f : F → E} {f' : F ≃L[𝕜] E} {a : E} {s : Set E} {t : Set F}

/-- If `f (g x) = x` for `x` in some neighborhood of `a`, `g` is continuous at `a`,
and `f` has an invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**HasFDerivAt.of_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.of_local_left_inverse (hg : ContinuousAt g a) (hf : HasFDerivA
t f (f' : F ->L[𝕜] E) (g a)) (hfg : forallᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt
 g (f'.symm : E ->L[𝕜] F) a
参数：hg : ContinuousAt g a；hf : HasFDerivAt f (f' : F ->L[𝕜] E) (g a)；hfg : forall
ᶠ y in 𝓝 a, f (g y) = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.of_comp_of_leftInverse`：HasFDerivAt.of_comp_of_leftInverse (
hgc : ContinuousAt g a) (hf : HasFDerivAt f f' (g a)) (hh : HasFDerivAt h h' a) 
(hcomp : f ∘ g =ᶠ[𝓝 a] h…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b

--- 原说明 ---
If `f (g x) = x` for `x` in some neighborhood of `a`, `g` is continuous at `a`,
and `f` has an invertible derivative `f'` at `g a`, then `g` has the derivative 
`f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem HasFDerivAt.of_local_left_inverse
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : F →L[𝕜] E) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : E →L[𝕜] F) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E →L[𝕜] F)) hg (hasFDerivAt_id _) hfg
    f'.symm_apply_apply

/-- If `f (g x) = x` for `x` in a neighborhood of `a` within `s`,
`g` maps a neighborhood of `a` within `s` to a neighborhood of `g a` within `t`,
and `f` has an invertible derivative `f'` at `g a` within `t`,
then `g` has the derivative `f'⁻¹` at `a` within `s`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
/-
**HasFDerivWithinAt.of_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_local_left_inverse (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g 
a))) (hf : HasFDerivWithinAt f (f' : F ->L[𝕜] E) t (g a)) (ha : a in s) (hfg : f
orallᶠ x in 𝓝[s] a, f (g x) = x) : HasFDerivWithinAt g (f'.symm : E ->L[𝕜] F) s 
a
参数：hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))；hf : HasFDerivWithinAt f (f' : F ->L[𝕜] 
E) t (g a)；ha : a in s；hfg : forallᶠ x in 𝓝[s] a, f (g x) = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_comp_of_leftInverse`：HasFDerivWithinAt.of_comp_of_l
eftInverse (hst : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f f' 
t (g a)) (hh : HasFDerivWithin…
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b

--- 原说明 ---
If `f (g x) = x` for `x` in a neighborhood of `a` within `s`,
`g` maps a neighborhood of `a` within `s` to a neighborhood of `g a` within `t`,
and `f` has an invertible derivative `f'` at `g a` within `t`,
then `g` has the derivative `f'⁻¹` at `a` within `s`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have an
inverse function.
-/
theorem HasFDerivWithinAt.of_local_left_inverse
    (hg : Tendsto g (𝓝[s] a) (𝓝[t] (g a))) (hf : HasFDerivWithinAt f (f' : F →L[𝕜] E) t (g a))
    (ha : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, f (g x) = x) :
    HasFDerivWithinAt g (f'.symm : E →L[𝕜] F) s a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : E →L[𝕜] F)) hg (hasFDerivWithinAt_id _ _) hfg
    f'.symm_apply_apply ha

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
/-
**HasStrictFDerivAt.of_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.of_local_left_inverse {f : E -> F} {f' : E ≃L[𝕜] F} {g :
 F -> E} {a : F} (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E ->L[𝕜
] F) (g a)) (hfg : forallᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm
 : F ->L[𝕜] E) a
参数：hg : ContinuousAt g a；hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) (g a)；hfg : 
forallᶠ y in 𝓝 a, f (g y) = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.of_comp_of_leftInverse`：HasStrictFDerivAt.of_comp_of_l
eftInverse (hgc : ContinuousAt g a) (hf : HasStrictFDerivAt f f' (g a)) (hh : Ha
sStrictFDerivAt h h' a) (hcomp…
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b

--- 原说明 ---
If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, 
and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the deriva
tive `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have an
inverse function.
-/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) a :=
  hf.of_comp_of_leftInverse (f'symm := (f'.symm : F →L[𝕜] E)) hg (hasStrictFDerivAt_id _) hfg
    f'.symm_apply_apply

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.hasStrictFDerivAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.hasStrictFDerivAt_symm (f : OpenPartialHomeomorph E 
F) {f' : E ≃L[𝕜] F} {a : F} (ha : a in f.target) (htff' : HasStrictFDerivAt f (f
' : E ->L[𝕜] F) (f.symm a)) : HasStrictFDerivAt f.symm (f'.symm : F ->L[𝕜] E) a
参数：f : OpenPartialHomeomorph E F；ha : a in f.target；htff' : HasStrictFDerivAt f 
(f' : E ->L[𝕜] F) (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.of_local_left_inverse`：HasStrictFDerivAt.of_local_left
_inverse {f : E -> F} {f' : E ≃L[𝕜] F} {g : F -> E} {a : F} (hg : ContinuousAt g
 a) (hf : HasStrictFDerivAt f…
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y

--- 原说明 ---
If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`
, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a
`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.hasStrictFDerivAt_symm (f : OpenPartialHomeomorph E F)
    {f' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
    (htff' : HasStrictFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasStrictFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.hasFDerivAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.hasFDerivAt_symm (f : OpenPartialHomeomorph E F) {f'
 : E ≃L[𝕜] F} {a : F} (ha : a in f.target) (htff' : HasFDerivAt f (f' : E ->L[𝕜]
 F) (f.symm a)) : HasFDerivAt f.symm (f'.symm : F ->L[𝕜] E) a
参数：f : OpenPartialHomeomorph E F；ha : a in f.target；htff' : HasFDerivAt f (f' : 
E ->L[𝕜] F) (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.of_local_left_inverse`：HasFDerivAt.of_local_left_inverse (hg
 : ContinuousAt g a) (hf : HasFDerivAt f (f' : F ->L[𝕜] E) (g a)) (hfg : forallᶠ
 y in 𝓝 a, f (g y) = y)…
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y

--- 原说明 ---
If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`
, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹
` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.hasFDerivAt_symm (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F}
    {a : F} (ha : a ∈ f.target) (htff' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) (f.eventually_right_inverse ha)
