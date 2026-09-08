/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Instances.Matrix

/-!
# Topology on matrix groups

Lemmas about the topology of matrix groups, such as `GL(n, R)` and `SL(n, R)` for a
topological ring `R`.
-/

public section

open Matrix Topology

variable {n R S : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S] {f : R →+* S}

/-!
### Topology of the general linear group
-/

namespace Matrix.GeneralLinearGroup

@[fun_prop]
/-
**Matrix.GeneralLinearGroup.continuous_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.G
eneralLinearGroup`。
形式化陈述：continuous_apply {α : Type*} [TopologicalSpace α] (f : α -> GL n R) (hf : 
Continuous f) (i : n) : Continuous (fun x => f x i)
参数：f : α -> GL n R；hf : Continuous f；i : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
-/
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → GL n R) (hf : Continuous f) (i : n) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

@[fun_prop]
/-
**Matrix.GeneralLinearGroup._root_.Continuous.generalLinearGroup_map** 是 Mathlib
 中的一个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Continuous.generalLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) :=
  (continuous_id.matrix_map hf).units_map
/-
**Matrix.GeneralLinearGroup._root_.Topology.IsInducing.generalLinearGroup_map** 
是 Mathlib 中的一个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsInducing.generalLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  hf.matrix_map.units_map
/-
**Matrix.GeneralLinearGroup._root_.Topology.IsEmbedding.generalLinearGroup_map**
 是 Mathlib 中的一个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsEmbedding.generalLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

variable [IsTopologicalRing R]
/-
**Matrix.GeneralLinearGroup._root_.Topology.IsClosedEmbedding.generalLinearGroup
_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsClosedEmbedding.generalLinearGroup_map [T0Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

/-- The determinant is continuous as a map from the general linear group to the units. -/
/-
**Matrix.GeneralLinearGroup.continuous_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Gen
eralLinearGroup`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R]   [inst_3 : TopologicalSpace R] [IsTopologicalRing R], C
ontinuous ⇑Matrix.GeneralLinearGroup.det
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Units.continuous_coe_inv`：continuous_coe_inv : Continuous (fun u => ↑u⁻¹
 : Mˣ -> M)

--- 原说明 ---
The determinant is continuous as a map from the general linear group to the unit
s.
-/
@[continuity, fun_prop] protected lemma continuous_det :
    Continuous (det : GL n R → Rˣ) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]
/-
**Matrix.GeneralLinearGroup.continuous_upperRightHom** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix.GeneralLinearGroup`。
形式化陈述：continuous_upperRightHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopo
logicalRing R] : Continuous (upperRightHom (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `Units.embedProduct_apply`：∀ (α : Type u_6) [inst : Monoid α] (x : αˣ), (
Units.embedProduct α) x = (↑x, MulOpposite.op ↑x⁻¹)
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
lemma continuous_upperRightHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (upperRightHom (R := R)) := by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg, continuous_id']

end Matrix.GeneralLinearGroup

/-!
### Topology of the special linear group
-/
namespace Matrix.SpecialLinearGroup

local notation "SL" => SpecialLinearGroup

/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (SL n R) :=
  inferInstanceAs <| TopologicalSpace (Subtype _)

@[fun_prop]
/-
**Matrix.SpecialLinearGroup.continuous_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：continuous_apply {α : Type*} [TopologicalSpace α] (f : α -> SL n R) (hf : 
Continuous f) (i) : Continuous (fun x => f x i)
参数：f : α -> SL n R；hf : Continuous f；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → SL n R) (hf : Continuous f) (i) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

/-- The topology on `SL n R` is functorial in `R`. -/
@[fun_prop]
/-
**Matrix.SpecialLinearGroup._root_.Continuous.specialLinearGroup_map** 是 Mathlib
 中的一个引理，位于命名空间 `Matrix.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on `SL n R` is functorial in `R`.
-/
lemma _root_.Continuous.specialLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) := by
  refine IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact (continuous_id.matrix_map hf).comp continuous_subtype_val
/-
**Matrix.SpecialLinearGroup._root_.Topology.IsInducing.specialLinearGroup_map** 
是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsInducing.specialLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val
/-
**Matrix.SpecialLinearGroup._root_.Topology.IsEmbedding.specialLinearGroup_map**
 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsEmbedding.specialLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

variable [IsTopologicalRing R]

/-- If `R` is a commutative ring with the discrete topology, then `SL(n, R)` has the discrete
topology. -/
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a commutative ring with the discrete topology, then `SL(n, R)` has the
 discrete
topology.
-/
instance [DiscreteTopology R] : DiscreteTopology (SL n R) :=
  inferInstanceAs <| DiscreteTopology (Subtype _)
/-
**Matrix.SpecialLinearGroup.isClosedEmbedding_val** 是 Mathlib 中的一个引理，位于命名空间 `Mat
rix.SpecialLinearGroup`。
形式化陈述：isClosedEmbedding_val [T1Space R] : IsClosedEmbedding ((↑) : SL n R -> Mat
rix n n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
lemma isClosedEmbedding_val [T1Space R] :
    IsClosedEmbedding ((↑) : SL n R → Matrix n n R) :=
  (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal
/-
**Matrix.SpecialLinearGroup._root_.Topology.IsClosedEmbedding.specialLinearGroup
_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsClosedEmbedding.specialLinearGroup_map [T1Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp isClosedEmbedding_val).of_comp .subtypeVal
/-
**Matrix.SpecialLinearGroup.instT1Space** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：instT1Space [T1Space R] : T1Space (SL n R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用引理 `Matrix.SpecialLinearGroup.isClosedEmbedding_val`：isClosedEmbedding_val [
T1Space R] : IsClosedEmbedding ((↑) : SL n R -> Matrix n n R)
-/
instance instT1Space [T1Space R] : T1Space (SL n R) := isClosedEmbedding_val.isEmbedding.t1Space

/-- The special linear group over a topological ring is a topological group. -/
/-
**Matrix.SpecialLinearGroup.topologicalGroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：topologicalGroup : IsTopologicalGroup (SL n R) where continuous_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `instContinuousMulMatrixOfContinuousAdd`：∀ {n : Type u_5} {R : Type u_8} 
[inst : TopologicalSpace R] [inst_1 : Fintype n] [inst_2 : Mul R]   [inst_3 : Ad
dCommMonoid R] [ContinuousAd…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Continuous.matrix_adjugate`：Continuous.matrix_adjugate [Fintype n] [Deci
dableEq n] [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Cont
inuous A) : Cont…

--- 原说明 ---
The special linear group over a topological ring is a topological group.
-/
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

/-!
### Mapping `SL(n, R)` to `GL(n, R)`
-/
section toGL

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
@[fun_prop]
/-
**Matrix.SpecialLinearGroup.continuous_toGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Sp
ecialLinearGroup`。
形式化陈述：continuous_toGL : Continuous (toGL : SL n R -> GL n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
The natural map from `SL n A` to `GL n A` is continuous.
-/
lemma continuous_toGL : Continuous (toGL : SL n R → GL n R) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/-- The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`. -/
/-
**Matrix.SpecialLinearGroup.isInducing_toGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Sp
ecialLinearGroup`。
形式化陈述：isInducing_toGL : IsInducing (toGL : SL n R -> GL n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用引理 `Matrix.SpecialLinearGroup.continuous_toGL`：continuous_toGL : Continuous 
(toGL : SL n R -> GL n R)
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f

--- 原说明 ---
The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`.
-/
lemma isInducing_toGL : IsInducing (toGL : SL n R → GL n R) :=
  .of_comp continuous_toGL Units.continuous_val (IsInducing.induced _)

/-- The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injection and
the topology on `SL n A` coincides with the subspace topology from `GL n A`. -/
/-
**Matrix.SpecialLinearGroup.isEmbedding_toGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：isEmbedding_toGL : IsEmbedding (toGL : SL n R -> GL n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.SpecialLinearGroup.isInducing_toGL`：isInducing_toGL : IsInducing 
(toGL : SL n R -> GL n R)
· 使用引理 `Matrix.SpecialLinearGroup.toGL_injective`：toGL_injective : Function.Inje
ctive (toGL : SpecialLinearGroup n R -> GL n R)

--- 原说明 ---
The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injecti
on and
the topology on `SL n A` coincides with the subspace topology from `GL n A`.
-/
lemma isEmbedding_toGL : IsEmbedding (toGL : SL n R → GL n R) :=
  ⟨isInducing_toGL, toGL_injective⟩
/-
**Matrix.SpecialLinearGroup.range_toGL** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Special
LinearGroup`。
形式化陈述：range_toGL {A : Type*} [CommRing A] : Set.range (toGL : SL n A -> GL n A) 
= GeneralLinearGroup.det ⁻¹' {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_toGL {A : Type*} [CommRing A] :
    Set.range (toGL : SL n A → GL n A) = GeneralLinearGroup.det ⁻¹' {1} := by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The natural inclusion of `SL n A` in `GL n A` is a closed embedding. -/
/-
**Matrix.SpecialLinearGroup.isClosedEmbedding_toGL** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.SpecialLinearGroup`。
形式化陈述：isClosedEmbedding_toGL [T0Space R] : IsClosedEmbedding (toGL : SL n R -> G
L n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.SpecialLinearGroup.isEmbedding_toGL`：isEmbedding_toGL : IsEmbeddi
ng (toGL : SL n R -> GL n R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.range_toGL`：range_toGL {A : Type*} [CommRing A
] : Set.range (toGL : SL n A -> GL n A) = GeneralLinearGroup.det ⁻¹' {1}
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Matrix.GeneralLinearGroup.continuous_det`：∀ {n : Type u_1} {R : Type u_2
} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [inst_3 : 
TopologicalSpace R] [IsTopolog…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R

--- 原说明 ---
The natural inclusion of `SL n A` in `GL n A` is a closed embedding.
-/
lemma isClosedEmbedding_toGL [T0Space R] : IsClosedEmbedding (toGL : SL n R → GL n R) :=
  ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage <| by fun_prop⟩

end toGL

section mapGL

/-!
### Shortcuts for the composite `SL(n, R) → GL(n, S)`
-/
variable [Algebra R S] [IsTopologicalRing S]

omit [IsTopologicalRing R]

/-
**Matrix.SpecialLinearGroup.continuous_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：continuous_mapGL [ContinuousSMul R S] : Continuous (mapGL S : SL n R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `Matrix.SpecialLinearGroup.continuous_toGL`：continuous_toGL : Continuous 
(toGL : SL n R -> GL n R)
· 使用定理 `Continuous.specialLinearGroup_map`：∀ {n : Type u_1} {R : Type u_2} {S : 
Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [i
nst_3 : TopologicalSpac…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_algebraMap_iff_smul`：continuous_algebraMap_iff_smul [Continuo
usMul A] : Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
lemma continuous_mapGL [ContinuousSMul R S] : Continuous (mapGL S : SL n R → _) :=
  continuous_toGL.comp
    (continuous_algebraMap_iff_smul R S |>.2 continuous_smul).specialLinearGroup_map
/-
**Matrix.SpecialLinearGroup.isInducing_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：isInducing_mapGL (h : IsInducing (algebraMap R S)) : IsInducing (mapGL S :
 SL n R -> _)
参数：h : IsInducing (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用引理 `Matrix.SpecialLinearGroup.isInducing_toGL`：isInducing_toGL : IsInducing 
(toGL : SL n R -> GL n R)
· 使用定理 `Topology.IsInducing.specialLinearGroup_map`：∀ {n : Type u_1} {R : Type u
_2} {S : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRin
g R]   [inst_3 : TopologicalSpac…
-/
lemma isInducing_mapGL (h : IsInducing (algebraMap R S)) :
    IsInducing (mapGL S : SL n R → _) :=
  isInducing_toGL.comp h.specialLinearGroup_map
/-
**Matrix.SpecialLinearGroup.isEmbedding_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.
SpecialLinearGroup`。
形式化陈述：isEmbedding_mapGL (h : IsEmbedding (algebraMap R S)) : IsEmbedding (mapGL 
S : SL n R -> _)
参数：h : IsEmbedding (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Matrix.SpecialLinearGroup.isEmbedding_toGL`：isEmbedding_toGL : IsEmbeddi
ng (toGL : SL n R -> GL n R)
· 使用定理 `Topology.IsEmbedding.specialLinearGroup_map`：∀ {n : Type u_1} {R : Type 
u_2} {S : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRi
ng R]   [inst_3 : TopologicalSpac…
-/
lemma isEmbedding_mapGL (h : IsEmbedding (algebraMap R S)) :
    IsEmbedding (mapGL S : SL n R → _) :=
  isEmbedding_toGL.comp h.specialLinearGroup_map
/-
**Matrix.SpecialLinearGroup.isClosedEmbedding_mapGL** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix.SpecialLinearGroup`。
形式化陈述：isClosedEmbedding_mapGL [IsTopologicalRing R] [T1Space R] [T1Space S] (h :
 IsClosedEmbedding (algebraMap R S)) : IsClosedEmbedding (mapGL S : SL n R -> _)
参数：h : IsClosedEmbedding (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用引理 `Matrix.SpecialLinearGroup.isClosedEmbedding_toGL`：isClosedEmbedding_toGL
 [T0Space R] : IsClosedEmbedding (toGL : SL n R -> GL n R)
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `Topology.IsClosedEmbedding.specialLinearGroup_map`：∀ {n : Type u_1} {R :
 Type u_2} {S : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : 
CommRing R]   [inst_3 : TopologicalSpac…
-/
lemma isClosedEmbedding_mapGL [IsTopologicalRing R] [T1Space R] [T1Space S]
    (h : IsClosedEmbedding (algebraMap R S)) :
    IsClosedEmbedding (mapGL S : SL n R → _) :=
  isClosedEmbedding_toGL.comp h.specialLinearGroup_map

end mapGL

end Matrix.SpecialLinearGroup

end

