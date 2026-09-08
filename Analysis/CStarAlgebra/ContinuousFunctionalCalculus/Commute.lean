/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Commuting with applications of the continuous functional calculus

This file shows that if an element `b` commutes with both `a` and `star a`, then it commutes
with `cfc f a` (or `cfcₙ f a`). In the case where `a` is selfadjoint, we may reduce the hypotheses.

## Main results

* `Commute.cfc` and `Commute.cfcₙ`: an element commutes with `cfc f a` or `cfcₙ f a` if it
  commutes with both `a` and `star a`. Specialized versions for `ℝ` and `ℝ≥0` or for
  `IsSelfAdjoint a` which do not require the user to show the element commutes with `star a` are
  provided for convenience.

## Implementation notes

The proof of `Commute.cfcHom` and `Commute.cfcₙHom` could be made simpler by appealing to basic
facts about double commutants, but doing so would require extra type class assumptions so that we
can talk about topological star algebras. Instead, we avoid this to minimize the work Lean must do
to call these lemmas, and give a straightforward proof by induction.

-/

public section

variable {𝕜 A : Type*}

open scoped NNReal

section Unital

section RCLike

variable {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [ContinuousFunctionalCalculus 𝕜 A p]
  [IsSemitopologicalRing A] [T2Space A]

open StarAlgebra.elemental in
/-
**Commute.cfcHom** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A} (ha : p a),   Commute a b → Commute (star a) b → ∀ (f : C(
↑(spectrum 𝕜 a), 𝕜)), Commute ((cfcHom ha) f) b
参数：ha : p a；star a；f : C(↑(spectrum 𝕜 a), 𝕜)；(cfcHom ha) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.induction_on_of_compact`：ContinuousMap.induction_on_of_com
pact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s] {p : C(s, 𝕜) -> Prop} (
const : forall r, p (.const…
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Commute.add_left`：add_left [Distrib R] {a b c : R} : Commute a c -> Comm
ute b c -> Commute (a + b) c
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Commute.mul_left`：mul_left (hac : Commute a c) (hbc : Commute b c) : Com
mute (a * b) c
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
（共 37 条，此处仅展示前 30 条）
-/
protected theorem Commute.cfcHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b := by
  open scoped ContinuousFunctionalCalculus in
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    conv =>
      enter [1, 2]
      equals algebraMap 𝕜 _ r => rfl
    rw [AlgHomClass.commutes]
    exact Algebra.commute_algebraMap_left r b
  | id => rwa [cfcHom_id ha]
  | star_id => rwa [map_star, cfcHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact mul_left hf hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_ofPred (p := fun x => x * b = b * x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    apply mem_closure_of_frequently_of_tendsto hf
    exact cfcHom_continuous ha |>.tendsto _
/-
**IsSelfAdjoint.commute_cfcHom** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A} (ha : p a),   IsSelfAdjoint a → Commute a b → ∀ (f : C(↑(s
pectrum 𝕜 a), 𝕜)), Commute ((cfcHom ha) f) b
参数：ha : p a；f : C(↑(spectrum 𝕜 a), 𝕜)；(cfcHom ha) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  hb.cfcHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfc f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `Commute (star a) b` hypothesis. -/
@[grind ←]
/-
**Commute.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, Commute a b → Commute (star a) b → ∀ (f : 𝕜 → 𝕜), Commute
 (cfc f a) b
参数：star a；f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…

--- 原说明 ---
An element commutes with `cfc f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal`
 which don't require
the `Commute (star a) b` hypothesis.
-/
protected theorem Commute.cfc {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ hb₁.cfcHom ha hb₂ ⟨_, hf.domRestrict⟩

/-- For `a` selfadjoint, an element commutes with `cfc f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfc f a = 0`). -/
/-
**IsSelfAdjoint.commute_cfc** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, IsSelfAdjoint a → Commute a b → ∀ (f : 𝕜 → 𝕜), Commute (c
fc f a) b
参数：f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Commute.cfc`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 :
 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x

--- 原说明 ---
For `a` selfadjoint, an element commutes with `cfc f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal`
 which don't require
the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfc f a = 0`).
-/
protected theorem IsSelfAdjoint.commute_cfc {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  hb₁.cfc (ha.star_eq.symm ▸ hb₁) f

end RCLike

section NNReal

variable [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction
with `star` when the base ring is `ℝ`. -/
@[grind ←]
/-
**Commute.cfc_real** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Algebra ℝ
 A] [inst_3 : TopologicalSpace A]   [inst_4 : ContinuousFunctionalCalculus ℝ A I
sSelfAdjoint] [IsTopologicalRing A] [T2Space A] {a b : A},   Commute a b → ∀ (f 
: ℝ → ℝ), Commute (cfc f a) b
参数：f : ℝ → ℝ；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `Commute.cfc`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 :
 …
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x

--- 原说明 ---
A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require
 any interaction
with `star` when the base ring is `ℝ`.
-/
protected theorem Commute.cfc_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _) fun hf ha ↦ by
    rw [← cfc_apply ..]
    exact hb.cfc (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction
with `star` when the base ring is `ℝ≥0`. -/
@[grind ←]
/-
**Commute.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Algebra ℝ
 A] [inst_3 : TopologicalSpace A]   [inst_4 : ContinuousFunctionalCalculus ℝ A I
sSelfAdjoint] [IsTopologicalRing A] [T2Space A] [inst_7 : PartialOrder A]   [ins
t_8 : NonnegSpectrumClass ℝ A] [inst_9 : StarOrderedRing A] {a b : A},   Commute
 a b → ∀ (f : NNReal → NNReal), Commute (cfc f a) b
参数：f : NNReal → NNReal；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Commute.cfc_real`：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarRing A]
 [inst_2 : Algebra ℝ A] [inst_3 : TopologicalSpace A]   [inst_4 : ContinuousFunc
tional…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0

--- 原说明 ---
A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require
 any interaction
with `star` when the base ring is `ℝ≥0`.
-/
protected theorem Commute.cfc_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfc f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfc_nnreal_eq_real ..]
    exact hb.cfc_real _
  · simp [cfc_apply_of_not_predicate a ha]

end NNReal

end Unital

section NonUnital

section RCLike

variable {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A]
variable [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus 𝕜 A p] [IsTopologicalRing A] [T2Space A]

open ContinuousMapZero

open NonUnitalStarAlgebra.elemental in
/-
**Commute.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, Commute a b → Commute (star a) b → ∀ (f : 𝕜 → 𝕜), Commute
 (cfc f a) b
参数：star a；f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
-/
protected theorem Commute.cfcₙHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp
  | smul r f hf => rw [map_smul]; exact hf.smul_left r
  | id => rwa [cfcₙHom_id ha]
  | star_id => rwa [map_star, cfcₙHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact mul_left hf hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_ofPred (p := fun x => x * b = b * x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    apply mem_closure_of_frequently_of_tendsto hf
    exact cfcₙHom_continuous ha |>.tendsto _
/-
**IsSelfAdjoint.commute_cfc** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, IsSelfAdjoint a → Commute a b → ∀ (f : 𝕜 → 𝕜), Commute (c
fc f a) b
参数：f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Commute.cfc`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 :
 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
protected theorem IsSelfAdjoint.commute_cfcₙHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  hb.cfcₙHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfcₙ f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't
require the `Commute (star a) b` hypothesis. -/
@[grind ←]
/-
**Commute.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, Commute a b → Commute (star a) b → ∀ (f : 𝕜 → 𝕜), Commute
 (cfc f a) b
参数：star a；f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…

--- 原说明 ---
An element commutes with `cfcₙ f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnrea
l` which don't
require the `Commute (star a) b` hypothesis.
-/
protected theorem Commute.cfcₙ {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf₀ ha ↦ hb₁.cfcₙHom ha hb₂ ⟨⟨_, hf.domRestrict⟩, hf₀⟩

/-- For `a` selfadjoint, an element commutes with `cfcₙ f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't
require the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfcₙ f a = 0`). -/
/-
**IsSelfAdjoint.commute_cfc** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, IsSelfAdjoint a → Commute a b → ∀ (f : 𝕜 → 𝕜), Commute (c
fc f a) b
参数：f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Commute.cfc`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 :
 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x

--- 原说明 ---
For `a` selfadjoint, an element commutes with `cfcₙ f a` if it commutes with `a`
.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnrea
l` which don't
require the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfcₙ f a =
 0`).
-/
protected theorem IsSelfAdjoint.commute_cfcₙ {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  hb₁.cfcₙ (ha.star_eq.symm ▸ hb₁) f

end RCLike

section NNReal

variable [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any
interaction with `star` when the base ring is `ℝ`. -/
@[grind ←]
/-
**Commute.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, Commute a b → Commute (star a) b → ∀ (f : 𝕜 → 𝕜), Commute
 (cfc f a) b
参数：star a；f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…

--- 原说明 ---
A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not requi
re any
interaction with `star` when the base ring is `ℝ`.
-/
protected theorem Commute.cfcₙ_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf0 ha ↦ by
      rw [← cfcₙ_apply ..]
      exact hb.cfcₙ (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any
interaction with `star` when the base ring is `ℝ≥0`. -/
@[grind ←]
/-
**Commute.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : RCLike 𝕜] [inst_1 :
 Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_4 : TopologicalSpa
ce A] [inst_5 : ContinuousFunctionalCalculus 𝕜 A p]   [IsSemitopologicalRing A] 
[T2Space A] {a b : A}, Commute a b → Commute (star a) b → ∀ (f : 𝕜 → 𝕜), Commute
 (cfc f a) b
参数：star a；f : 𝕜 → 𝕜；cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Commute.cfcHom`：∀ {𝕜 : Type u_1} {A : Type u_2} {p : A → Prop} [inst : R
CLike 𝕜] [inst_1 : Ring A] [inst_2 : StarRing A]   [inst_3 : Algebra 𝕜 A] [inst_
4 : …
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…

--- 原说明 ---
A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not requi
re any
interaction with `star` when the base ring is `ℝ≥0`.
-/
protected theorem Commute.cfcₙ_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfcₙ f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfcₙ_nnreal_eq_real ..]
    exact hb.cfcₙ_real _
  · simp [cfcₙ_apply_of_not_predicate a ha]

end NNReal

end NonUnital

