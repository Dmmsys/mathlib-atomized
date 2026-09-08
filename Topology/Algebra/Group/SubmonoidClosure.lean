/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topological closure of the submonoid closure

In this file we prove several versions of the following statement:
if `G` is a compact topological group and `s : Set G`,
then the topological closures of `Submonoid.closure s` and `Subgroup.closure s` are equal.

The proof is based on the following observation, see `mapClusterPt_self_zpow_atTop_pow`:
each `x^m`, `m : ℤ` is a limit point (`MapClusterPt`) of the sequence `x^n`, `n : ℕ`, as `n → ∞`.
-/

public section

open Filter Function Set
open scoped Topology

variable {G : Type*}

@[to_additive]
/-
**mapClusterPt_atTop_zpow_iff_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_atTop_zpow_iff_pow [DivInvMonoid G] [TopologicalSpace G] {x y
 : G} : MapClusterPt x atTop (y ^ · : Int -> G) ↔ MapClusterPt x atTop (y ^ · : 
Nat -> G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mapClusterPt_atTop_zpow_iff_pow [DivInvMonoid G] [TopologicalSpace G] {x y : G} :
    MapClusterPt x atTop (y ^ · : ℤ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

variable [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]

@[to_additive]
/-
**mapClusterPt_self_zpow_atTop_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_self_zpow_atTop_pow (x : G) (m : Int) : MapClusterPt (x ^ m) 
atTop (x ^ · : Nat -> G)
参数：x : G；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_clusterPt_of_compactSpace`：exists_clusterPt_of_compactSpace [Comp
actSpace X] (f : Filter X) [NeBot f] : exists x, ClusterPt x f
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mapClusterPt_atTop_zpow_iff_pow`：mapClusterPt_atTop_zpow_iff_pow [DivInv
Monoid G] [TopologicalSpace G] {x y : G} : MapClusterPt x atTop (y ^ · : Int -> 
G) ↔ MapClusterPt x a…
· 使用定理 `ContinuousAt.fun_div'`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Div G]   [ContinuousDiv G] {f
 g : X → G}…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用定理 `ContinuousAt.const_mul`：ContinuousAt.const_mul (hf : ContinuousAt f x) (
b : M) : ContinuousAt (b * f ·) x
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `ContinuousAt.fst`：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).1) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MapClusterPt.continuousAt_comp`：MapClusterPt.continuousAt_comp [Topologi
calSpace Y] {f : X -> Y} (hf : ContinuousAt f x) (hu : MapClusterPt x F u) : Map
ClusterPt (f x) F (f…
· 使用定理 `MapClusterPt.curry_prodMap`：MapClusterPt.curry_prodMap {α β : Type*} {f 
: α -> X} {g : β -> Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y} (hf : Map
ClusterPt x la f…
· 使用定理 `Filter.Tendsto.curry`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f 
: α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ},   (∀ᶠ (a : α) in l
a, Filter.…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.tendsto_atTop_add_const_left`：∀ {α : Type u_1} {G : Type u_2} [in
st : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filte
r α)   {f : α → G} (C : G…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
（共 31 条，此处仅展示前 30 条）
-/
theorem mapClusterPt_self_zpow_atTop_pow (x : G) (m : ℤ) :
    MapClusterPt (x ^ m) atTop (x ^ · : ℕ → G) := by
  obtain ⟨y, hy⟩ : ∃ y, MapClusterPt y atTop (x ^ · : ℤ → G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b ↦ x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz ↦ x ^ m * yz.2 / yz.1) (y, y) := by fun_prop
    simpa only [comp_def, ← zpow_sub, ← zpow_add, div_eq_mul_inv, Prod.map, mul_inv_cancel_right]
      using! (hy.curry_prodMap hy).continuousAt_comp this
  suffices Tendsto ↿(fun a b ↦ m + b - a) (atTop.curry atTop) atTop from H.of_comp this
  refine Tendsto.curry <| .of_forall fun a ↦ ?_
  simp only [sub_eq_add_neg] -- TODO: add `Tendsto.atTop_sub_const` etc
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left atTop m tendsto_id)

@[to_additive]
/-
**mapClusterPt_one_atTop_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_one_atTop_pow (x : G) : MapClusterPt 1 atTop (x ^ · : Nat -> 
G)
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mapClusterPt_self_zpow_atTop_pow`：mapClusterPt_self_zpow_atTop_pow (x : 
G) (m : Int) : MapClusterPt (x ^ m) atTop (x ^ · : Nat -> G)
-/
theorem mapClusterPt_one_atTop_pow (x : G) : MapClusterPt 1 atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]
/-
**mapClusterPt_self_atTop_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_self_atTop_pow (x : G) : MapClusterPt x atTop (x ^ · : Nat ->
 G)
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mapClusterPt_self_zpow_atTop_pow`：mapClusterPt_self_zpow_atTop_pow (x : 
G) (m : Int) : MapClusterPt (x ^ m) atTop (x ^ · : Nat -> G)
-/
theorem mapClusterPt_self_atTop_pow (x : G) : MapClusterPt x atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]
/-
**mapClusterPt_atTop_pow_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_atTop_pow_tfae (x y : G) : List.TFAE [ MapClusterPt x atTop (
y ^ · : Nat -> G), MapClusterPt x atTop (y ^ · : Int -> G), x in closure (range 
(y ^ · : Nat -> G)), x in closure (range (y ^ · : Int -> G)), ]
参数：x y : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mapClusterPt_atTop_zpow_iff_pow`：mapClusterPt_atTop_zpow_iff_pow [DivInv
Monoid G] [TopologicalSpace G] {x y : G} : MapClusterPt x atTop (y ^ · : Int -> 
G) ↔ MapClusterPt x a…
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `mapClusterPt_self_zpow_atTop_pow`：mapClusterPt_self_zpow_atTop_pow (x : 
G) (m : Int) : MapClusterPt (x ^ m) atTop (x ^ · : Nat -> G)
· 使用定理 `isClosed_setOfPred_clusterPt`：isClosed_setOfPred_clusterPt {f : Filter X
} : IsClosed { x | ClusterPt x f }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mapClusterPt_atTop_pow_tfae (x y : G) :
    List.TFAE [
      MapClusterPt x atTop (y ^ · : ℕ → G),
      MapClusterPt x atTop (y ^ · : ℤ → G),
      x ∈ closure (range (y ^ · : ℕ → G)),
      x ∈ closure (range (y ^ · : ℤ → G)),
    ] := by
  tfae_have 2 ↔ 1 := mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 → 4 := by
    refine fun h ↦ closure_mono (range_subset_iff.2 fun n ↦ ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 → 1 := by
    refine fun h ↦ closure_minimal ?_ isClosed_setOfPred_clusterPt h
    exact range_subset_iff.2 (mapClusterPt_self_zpow_atTop_pow _)
  tfae_have 1 → 3 := by
    rw [mem_closure_iff_clusterPt]
    exact (ClusterPt.mono · (le_principal_iff.2 range_mem_map))
  tfae_finish

@[to_additive]
/-
**mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers {x y : G} : MapC
lusterPt x atTop (y ^ · : Nat -> G) ↔ x in (Subgroup.zpowers y).topologicalClosu
re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `mapClusterPt_atTop_pow_tfae`：mapClusterPt_atTop_pow_tfae (x y : G) : Lis
t.TFAE [ MapClusterPt x atTop (y ^ · : Nat -> G), MapClusterPt x atTop (y ^ · : 
Int -> G), x in c…
-/
theorem mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers {x y : G} :
    MapClusterPt x atTop (y ^ · : ℕ → G) ↔ x ∈ (Subgroup.zpowers y).topologicalClosure :=
  (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]
/-
**mapClusterPt_inv_atTop_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_inv_atTop_pow {x y : G} : MapClusterPt x⁻¹ atTop (y ^ · : Nat
 -> G) ↔ MapClusterPt x atTop (y ^ · : Nat -> G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mapClusterPt_inv_atTop_pow {x y : G} :
    MapClusterPt x⁻¹ atTop (y ^ · : ℕ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]
/-
**closure_range_zpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_range_zpow_eq_pow (x : G) : closure (range (x ^ · : Int -> G)) = c
losure (range (x ^ · : Nat -> G))
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `mapClusterPt_atTop_pow_tfae`：mapClusterPt_atTop_pow_tfae (x y : G) : Lis
t.TFAE [ MapClusterPt x atTop (y ^ · : Nat -> G), MapClusterPt x atTop (y ^ · : 
Int -> G), x in c…
-/
theorem closure_range_zpow_eq_pow (x : G) :
    closure (range (x ^ · : ℤ → G)) = closure (range (x ^ · : ℕ → G)) := by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]
/-
**denseRange_zpow_iff_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_zpow_iff_pow {x : G} : DenseRange (x ^ · : Int -> G) ↔ DenseRan
ge (x ^ · : Nat -> G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_range_zpow_eq_pow`：closure_range_zpow_eq_pow (x : G) : closure (
range (x ^ · : Int -> G)) = closure (range (x ^ · : Nat -> G))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem denseRange_zpow_iff_pow {x : G} :
    DenseRange (x ^ · : ℤ → G) ↔ DenseRange (x ^ · : ℕ → G) := by
  simp only [DenseRange, dense_iff_closure_eq, closure_range_zpow_eq_pow]

@[to_additive]
/-
**topologicalClosure_subgroupClosure_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalClosure_subgroupClosure_toSubmonoid (s : Set G) : (Subgroup.clo
sure s).toSubmonoid.topologicalClosure = (Submonoid.closure s).topologicalClosur
e
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Submonoid.topologicalClosure_minimal`：Submonoid.topologicalClosure_minim
al (s : Submonoid M) {t : Submonoid M} (h : s <= t) (ht : IsClosed (t : Set M)) 
: s.topologicalClosure <= …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inv`：mem_inv : a in s⁻¹ ↔ a⁻¹ in s
· 使用定理 `Submonoid.coe_powers`：coe_powers (x : M) : ↑(powers x) = Set.range fun n
 : Nat => x ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_range_zpow_eq_pow`：closure_range_zpow_eq_pow (x : G) : closure (
range (x ^ · : Int -> G)) = closure (range (x ^ · : Nat -> G))
· 使用定理 `Subgroup.coe_zpowers`：coe_zpowers (g : G) : ↑(zpowers g) = Set.range (g 
^ · : Int -> G)
· 使用定理 `Subgroup.topologicalClosure_coe`：Subgroup.topologicalClosure_coe {s : Su
bgroup G} : (s.topologicalClosure : Set G) = _root_.closure s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Subgroup.le_closure_toSubmonoid`：le_closure_toSubmonoid (S : Set G) : Su
bmonoid.closure S <= (closure S).toSubmonoid
-/
theorem topologicalClosure_subgroupClosure_toSubmonoid (s : Set G) :
    (Subgroup.closure s).toSubmonoid.topologicalClosure =
      (Submonoid.closure s).topologicalClosure := by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid, Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx ↦ ?_
  refine closure_mono (Submonoid.powers_le.2 (Submonoid.subset_closure <| Set.mem_inv.1 hx)) ?_
  rw [Submonoid.coe_powers, ← closure_range_zpow_eq_pow, ← Subgroup.coe_zpowers,
    ← Subgroup.topologicalClosure_coe, SetLike.mem_coe, ← inv_mem_iff]
  exact subset_closure <| Subgroup.mem_zpowers _

@[to_additive]
/-
**closure_submonoidClosure_eq_closure_subgroupClosure** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：closure_submonoidClosure_eq_closure_subgroupClosure (s : Set G) : closure 
(Submonoid.closure s : Set G) = closure (Subgroup.closure s)
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `topologicalClosure_subgroupClosure_toSubmonoid`：topologicalClosure_subgr
oupClosure_toSubmonoid (s : Set G) : (Subgroup.closure s).toSubmonoid.topologica
lClosure = (Submonoid.closure s).top…
-/
theorem closure_submonoidClosure_eq_closure_subgroupClosure (s : Set G) :
    closure (Submonoid.closure s : Set G) = closure (Subgroup.closure s) :=
  congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]
/-
**dense_submonoidClosure_iff_subgroupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_submonoidClosure_iff_subgroupClosure {s : Set G} : Dense (Submonoid.
closure s : Set G) ↔ Dense (Subgroup.closure s : Set G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_submonoidClosure_eq_closure_subgroupClosure`：closure_submonoidCl
osure_eq_closure_subgroupClosure (s : Set G) : closure (Submonoid.closure s : Se
t G) = closure (Subgroup.closure s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dense_submonoidClosure_iff_subgroupClosure {s : Set G} :
    Dense (Submonoid.closure s : Set G) ↔ Dense (Subgroup.closure s : Set G) := by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]
