/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johan Commelin
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.CPolynomialDef
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Composition of analytic functions

In this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.compAlongComposition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : Composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `Composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `HasFPowerSeriesAt.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `AnalyticAt.comp` states that the composition of analytic functions is analytic.
* `FormalMultilinearSeries.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.compAlongComposition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `Composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, Composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `Composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`Composition.sigmaEquivSigmaPi` between `(Σ (a : Composition n), Composition a.length)` and
`(Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i))`, and is described
in more details below in the paragraph on associativity.
-/

@[expose] public section


noncomputable section

variable {𝕜 : Type*} {E F G H : Type*}

open Filter List

open scoped Topology NNReal ENNReal

section Topological

variable [CommRing 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

/-! ### Composing formal multilinear series -/


namespace FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/


/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyComposition c v i` for `v : Fin n → E` and `i : Fin c.length`. -/
/-
**FormalMultilinearSeries.applyComposition** 是 Mathlib 中的一个定义，位于命名空间 `FormalMult
ilinearSeries`。
形式化陈述：applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Compos
ition n) : (Fin n -> E) -> Fin c.length -> F
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal multilinear series `p`, a composition `c` of `n` and the index `i
` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables i
n the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. Th
is function is
called `p.applyComposition c v i` for `v : Fin n → E` and `i : Fin c.length`.
-/
def applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
    (Fin n → E) → Fin c.length → F := fun v i => p (c.blocksFun i) (v ∘ c.embedding i)
/-
**FormalMultilinearSeries.applyComposition_ones** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：applyComposition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) : p.ap
plyComposition (Composition.ones n) = fun v i => p 1 fun _ => v (Fin.castLE (Com
position.length_le _) i)
参数：p : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Composition.length_le`：length_le : c.length <= n
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Composition.ones_blocksFun`：ones_blocksFun (n : Nat) (i : Fin (ones n).l
ength) : (ones n).blocksFun i = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Fin.val_castLE`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), ↑(Fin.castLE h i) =
 ↑i
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Composition.ones_embedding`：ones_embedding (i : Fin (ones n).length) (h 
: 0 < (ones n).blocksFun i) : (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i
.2 (ones n).leng…
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem applyComposition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.applyComposition (Composition.ones n) = fun v i =>
      p 1 fun _ => v (Fin.castLE (Composition.length_le _) i) := by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by lia
  refine congr_arg v ?_
  rw [Fin.ext_iff, Fin.val_castLE, Composition.ones_embedding, Fin.val_mk]
/-
**FormalMultilinearSeries.applyComposition_single** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：applyComposition_single (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn 
: 0 < n) (v : Fin n -> E) : p.applyComposition (Composition.single n hn) v = fun
 _j => p n v
参数：p : FormalMultilinearSeries 𝕜 E F；hn : 0 < n；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.single_blocksFun`：single_blocksFun {n : Nat} (h : 0 < n) (i 
: Fin (single n h).length) : (single n h).blocksFun i = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `Composition.single_embedding`：single_embedding {n : Nat} (h : 0 < n) (i 
: Fin n) : ((single n h).embedding (0 : Fin 1)) i = i
-/
theorem applyComposition_single (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : 0 < n)
    (v : Fin n → E) : p.applyComposition (Composition.single n hn) v = fun _j => p n v := by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert! Composition.single_embedding hn ⟨i, hi2⟩ using 1
  obtain ⟨j_val, j_property⟩ := j
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  rw! [this]
  rfl

@[simp]
/-
**FormalMultilinearSeries.removeZero_applyComposition** 是 Mathlib 中的一个定理，位于命名空间 
`FormalMultilinearSeries`。
形式化陈述：removeZero_applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} 
(c : Composition n) : p.removeZero.applyComposition c = p.applyComposition c
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.removeZero_of_pos`：removeZero_of_pos (p : Formal
MultilinearSeries 𝕜 E F) {n : Nat} (h : 0 < n) : p.removeZero n = p n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Composition.one_le_blocksFun`：one_le_blocksFun (i : Fin c.length) : 1 <=
 c.blocksFun i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem removeZero_applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (c : Composition n) : p.removeZero.applyComposition c = p.applyComposition c := by
  ext v i
  simp [applyComposition, zero_lt_one.trans_le (c.one_le_blocksFun i), removeZero_of_pos]

/-- Technical lemma stating how `p.applyComposition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyComposition` retain
multilinearity. -/
/-
**FormalMultilinearSeries.applyComposition_update** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：applyComposition_update (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c :
 Composition n) (j : Fin n) (v : Fin n -> E) (z : E) : p.applyComposition c (Fun
ction.update v j z) = Function.update (p.applyComposition c v) (c.index j) (p (c
.blocksFun (c.index j)) (Function.update (v ∘ c.embedding (c.index j)) (c.invEmb
edding j) z))
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n；j : Fin n；v : Fin n -> E；
z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_comp_eq_of_injective`：update_comp_eq_of_injective {β : S
ort*} (g : α' -> β) {f : α -> α'} (hf : Function.Injective f) (i : α) (a : β) : 
Function.update g (f i) a …
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.embedding_comp_inv`：embedding_comp_inv (j : Fin n) : c.embed
ding (c.index j) (c.invEmbedding j) = j
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.update_comp_eq_of_notMem_range`：update_comp_eq_of_notMem_range 
{α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β] (g : β -> γ) {f : α -> β} {i
 : β} (a : γ) (h : i ∉ Set.ra…
· 使用定理 `Composition.mem_range_embedding_iff'`：mem_range_embedding_iff' {j : Fin 
n} {i : Fin c.length} : j in Set.range (c.embedding i) ↔ i = c.index j

--- 原说明 ---
Technical lemma stating how `p.applyComposition` commutes with updating variable
s. This
will be the key point to show that functions constructed from `applyComposition`
 retain
multilinearity.
-/
theorem applyComposition_update (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n)
    (j : Fin n) (v : Fin n → E) (z : E) :
    p.applyComposition c (Function.update v j z) =
      Function.update (p.applyComposition c v) (c.index j)
        (p (c.blocksFun (c.index j))
          (Function.update (v ∘ c.embedding (c.index j)) (c.invEmbedding j) z)) := by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) → Fin n := c.embedding (c.index j)
    simp only [Function.update_self]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update v j z ∘ r = Function.update (v ∘ r) j' z by rw [B]
    suffices C : Function.update v (r j') z ∘ r = Function.update (v ∘ r) j' z by
      convert! C; exact (c.embedding_comp_inv j).symm
    exact Function.update_comp_eq_of_injective _ (c.embedding _).injective _ _
  · simp only [h, Function.update_of_ne, Ne, not_false_iff]
    let r : Fin (c.blocksFun k) → Fin n := c.embedding k
    change p (c.blocksFun k) (Function.update v j z ∘ r) = p (c.blocksFun k) (v ∘ r)
    suffices B : Function.update v j z ∘ r = v ∘ r by rw [B]
    apply Function.update_comp_eq_of_notMem_range
    rwa [c.mem_range_embedding_iff']

@[simp]
/-
**FormalMultilinearSeries.compContinuousLinearMap_applyComposition** 是 Mathlib 中
的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：compContinuousLinearMap_applyComposition {n : Nat} (p : FormalMultilinearS
eries 𝕜 F G) (f : E ->L[𝕜] F) (c : Composition n) (v : Fin n -> E) : (p.compCont
inuousLinearMap f).applyComposition c v = p.applyComposition c (f ∘ v)
参数：p : FormalMultilinearSeries 𝕜 F G；f : E ->L[𝕜] F；c : Composition n；v : Fin n 
-> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compContinuousLinearMap_applyComposition {n : ℕ} (p : FormalMultilinearSeries 𝕜 F G)
    (f : E →L[𝕜] F) (c : Composition n) (v : Fin n → E) :
    (p.compContinuousLinearMap f).applyComposition c v = p.applyComposition c (f ∘ v) := by
  ext
  simp [applyComposition, Function.comp_def]

@[simp]
/-
**FormalMultilinearSeries.applyComposition_apply_prod** 是 Mathlib 中的一个定理，位于命名空间 
`FormalMultilinearSeries`。
形式化陈述：applyComposition_apply_prod {H : Type*} [CommRing H] [Algebra 𝕜 H] [Topolo
gicalSpace H] [IsTopologicalRing H] [ContinuousConstSMul 𝕜 H] (p : FormalMultili
nearSeries 𝕜 E H) {n : Nat} (c : Composition n) (v : Fin n -> E) : ∏ i, p.applyC
omposition c v i = ∏ i, p (c.blocksFun i) (v ∘ c.embedding i)
参数：p : FormalMultilinearSeries 𝕜 E H；c : Composition n；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
-/
theorem applyComposition_apply_prod {H : Type*} [CommRing H] [Algebra 𝕜 H] [TopologicalSpace H]
    [IsTopologicalRing H] [ContinuousConstSMul 𝕜 H] (p : FormalMultilinearSeries 𝕜 E H) {n : ℕ}
    (c : Composition n) (v : Fin n → E) :
    ∏ i, p.applyComposition c v i = ∏ i, p (c.blocksFun i) (v ∘ c.embedding i) := by
  rfl

end FormalMultilinearSeries

namespace ContinuousMultilinearMap

open FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a continuous multilinear map in `n` variables by
applying the right coefficient of `p` to each block of the composition, and then applying `f` to
the resulting vector. It is called `f.compAlongComposition p c`. -/
/-
**ContinuousMultilinearMap.compAlongComposition** 是 Mathlib 中的一个定义，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：compAlongComposition {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Co
mposition n) (f : F [×c.length]->L[𝕜] G) : E [×n]->L[𝕜] G where toMultilinearMap
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n；f : F [×c.length]->L[𝕜] G
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal multilinear series `p`, a composition `c` of `n` and a continuous
 multilinear
map `f` in `c.length` variables, one may form a continuous multilinear map in `n
` variables by
applying the right coefficient of `p` to each block of the composition, and then
 applying `f` to
the resulting vector. It is called `f.compAlongComposition p c`.
-/
def compAlongComposition {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) : E [×n]→L[𝕜] G where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ f (p.applyComposition c v))
      (fun v i x y ↦ by simp only [applyComposition_update, map_update_add])
      (fun v i c x ↦ by simp only [applyComposition_update, map_update_smul])
  cont :=
    f.cont.comp <|
      continuous_pi fun _ => (coe_continuous _).comp <| continuous_pi fun _ => continuous_apply _

@[simp]
/-
**ContinuousMultilinearMap.compAlongComposition_apply** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：compAlongComposition_apply {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (
c : Composition n) (f : F [×c.length]->L[𝕜] G) (v : Fin n -> E) : (f.compAlongCo
mposition p c) v = f (p.applyComposition c v)
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n；f : F [×c.length]->L[𝕜] G
；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem compAlongComposition_apply {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) (v : Fin n → E) :
    (f.compAlongComposition p c) v = f (p.applyComposition c v) :=
  rfl

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
/-
**FormalMultilinearSeries.compAlongComposition** 是 Mathlib 中的一个定义，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：compAlongComposition {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p : Fo
rmalMultilinearSeries 𝕜 E F) (c : Composition n) : (E [×n]->L[𝕜] G)
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Compo
sition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two formal multilinear series `q` and `p` and a composition `c` of `n`, on
e may
form a continuous multilinear map in `n` variables by applying the right coeffic
ient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector
. It is
called `q.compAlongComposition p c`.
-/
def compAlongComposition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) : (E [×n]→L[𝕜] G) :=
  (q c.length).compAlongComposition p c

@[simp]
/-
**FormalMultilinearSeries.compAlongComposition_apply** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：compAlongComposition_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (
p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) (v : Fin n -> E) : (q.com
pAlongComposition p c) v = q c.length (p.applyComposition c v)
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Compo
sition n；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem compAlongComposition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) (v : Fin n → E) :
    (q.compAlongComposition p c) v = q c.length (p.applyComposition c v) :=
  rfl

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.compAlongComposition p c` over all compositions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} qₖ (p_{i_1} (...), ..., p_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.

In general, the composition `q ∘ p` only makes sense when the constant coefficient of `p` vanishes.
We give a general formula but which ignores the value of `p 0` instead.
-/
/-
**FormalMultilinearSeries.comp** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSerie
s`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       {G : Type u
_4} →         [inst : CommRing 𝕜] →           [inst_1 : AddCommGroup E] →       
      [inst_2 : AddCommGroup F] →               [inst_3 : AddCommGroup G] →     
            [inst_4 : _root_.Module 𝕜 E] →                   [inst_5 : _root_.Mo
dule 𝕜 F] →                     [inst_6 : _root_.Module 𝕜 G] →                  
     [inst_7 : TopologicalSpace E] →                         [inst_8 : Topologic
alSpace F] →                           [inst_9 : TopologicalSpace G] →          
                   [inst_10 : IsTopologicalAddGroup E] →                        
       [inst_11 : ContinuousConstSMul 𝕜 E] →                                 [in
st_12 : IsTopologicalAddGroup F] →                                   [inst_13 : 
ContinuousConstSMul 𝕜 F] →                                     [inst_14 : IsTopo
logicalAddGroup G] →                                       [inst_15 : Continuous
ConstSMul 𝕜 G] →                                         FormalMultilinearSeries
 𝕜 F G →                                           FormalMultilinearSeries 𝕜 E F
 → FormalMultilinearSeries 𝕜 E G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal composition of two formal multilinear series. The `n`-th coefficient in t
he composition
is defined to be the sum of `q.compAlongComposition p c` over all compositions o
f
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., 
v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} qₖ (p_{i_1} (...), ..., p_{i_k} (...))`, where on
e puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.

In general, the composition `q ∘ p` only makes sense when the constant coefficie
nt of `p` vanishes.
We give a general formula but which ignores the value of `p 0` instead.
-/
protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => ∑ c : Composition n, q.compAlongComposition p c

/-- The `0`-th coefficient of `q.comp p` is `q 0`. Since these maps are multilinear maps in zero
variables, but on different spaces, we cannot state this directly, so we state it when applied to
arbitrary vectors (which have to be the zero vector). -/
/-
**FormalMultilinearSeries.comp_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：comp_coeff_zero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinear
Series 𝕜 E F) (v : Fin 0 -> E) (v' : Fin 0 -> F) : (q.comp p) 0 v = q 0 v'
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；v : Fin 0
 -> E；v' : Fin 0 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `composition_card`：composition_card (n : Nat) : Fintype.card (Composition
 n) = 2 ^ (n - 1)
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `FormalMultilinearSeries.compAlongComposition_apply`：compAlongComposition
_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSerie
s 𝕜 E F) (c : Composition n) (v : Fin n …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.helim`：∀ {α β : Sort u} [Meta.FastSubsingleto
n α], α = β → ∀ (a : α) (b : β), a ≍ b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `Lean.Meta.instFastIsEmptyFinOfNatNat`：Meta.FastIsEmpty (Fin 0)
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'

--- 原说明 ---
The `0`-th coefficient of `q.comp p` is `q 0`. Since these maps are multilinear 
maps in zero
variables, but on different spaces, we cannot state this directly, so we state i
t when applied to
arbitrary vectors (which have to be the zero vector).
-/
theorem comp_coeff_zero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 → E) (v' : Fin 0 → F) : (q.comp p) 0 v = q 0 v' := by
  let c : Composition 0 := Composition.ones 0
  dsimp [FormalMultilinearSeries.comp]
  have : {c} = (Finset.univ : Finset (Composition 0)) := by
    apply Finset.eq_of_subset_of_card_le <;> simp [Finset.card_univ, composition_card 0]
  rw [← this, Finset.sum_singleton, compAlongComposition_apply]
  symm; congr!

@[simp]
/-
**FormalMultilinearSeries.comp_coeff_zero'** 是 Mathlib 中的一个定理，位于命名空间 `FormalMult
ilinearSeries`。
形式化陈述：comp_coeff_zero' (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinea
rSeries 𝕜 E F) (v : Fin 0 -> E) : (q.comp p) 0 v = q 0 fun _i => 0
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；v : Fin 0
 -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `FormalMultilinearSeries.comp_coeff_zero`：comp_coeff_zero (q : FormalMult
ilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 -> E) (v' : 
Fin 0 -> F) : (q.comp p) 0 v …
-/
theorem comp_coeff_zero' (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 → E) : (q.comp p) 0 v = q 0 fun _i => 0 :=
  q.comp_coeff_zero p v _

/-- The `0`-th coefficient of `q.comp p` is `q 0`. When `p` goes from `E` to `E`, this can be
expressed as a direct equality -/
/-
**FormalMultilinearSeries.comp_coeff_zero''** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：comp_coeff_zero'' (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultiline
arSeries 𝕜 E E) : (q.comp p) 0 = q 0
参数：q : FormalMultilinearSeries 𝕜 E F；p : FormalMultilinearSeries 𝕜 E E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `FormalMultilinearSeries.comp_coeff_zero`：comp_coeff_zero (q : FormalMult
ilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 -> E) (v' : 
Fin 0 -> F) : (q.comp p) 0 v …

--- 原说明 ---
The `0`-th coefficient of `q.comp p` is `q 0`. When `p` goes from `E` to `E`, th
is can be
expressed as a direct equality
-/
theorem comp_coeff_zero'' (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E) :
    (q.comp p) 0 = q 0 := by ext v; exact q.comp_coeff_zero p _ _

/-- The first coefficient of a composition of formal multilinear series is the composition of the
first coefficients seen as continuous linear maps. -/
/-
**FormalMultilinearSeries.comp_coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：comp_coeff_one (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearS
eries 𝕜 E F) (v : Fin 1 -> E) : (q.comp p) 1 v = q 1 fun _i => p 1 v
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；v : Fin 1
 -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Finset.eq_univ_of_card`：Finset.eq_univ_of_card [Fintype α] (s : Finset α
) (hs : #s = Fintype.card α) : s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `composition_card`：composition_card (n : Nat) : Fintype.card (Composition
 n) = 2 ^ (n - 1)
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Composition.ones_length`：ones_length (n : Nat) : (ones n).length = n
· 使用定理 `Composition.length_le`：length_le : c.length <= n
· 使用定理 `FormalMultilinearSeries.applyComposition_ones`：applyComposition_ones (p 
: FormalMultilinearSeries 𝕜 E F) (n : Nat) : p.applyComposition (Composition.one
s n) = fun v i => p 1 fun _ => v (F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonFinOfNatNat`：Meta.FastSubsingleton (Fin 1)

--- 原说明 ---
The first coefficient of a composition of formal multilinear series is the compo
sition of the
first coefficients seen as continuous linear maps.
-/
theorem comp_coeff_one (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 1 → E) : (q.comp p) 1 v = q 1 fun _i => p 1 v := by
  have : {Composition.ones 1} = (Finset.univ : Finset (Composition 1)) :=
    Finset.eq_univ_of_card _ (by simp [composition_card])
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ← this,
    Finset.sum_singleton]
  refine q.congr (by simp) fun i hi1 hi2 => ?_
  simp only [applyComposition_ones]
  exact p.congr rfl fun j _hj1 hj2 => by congr!

/-- Only `0`-th coefficient of `q.comp p` depends on `q 0`. -/
/-
**FormalMultilinearSeries.removeZero_comp_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：removeZero_comp_of_pos (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMult
ilinearSeries 𝕜 E F) {n : Nat} (hn : 0 < n) : q.removeZero.comp p n = q.comp p n
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；hn : 0 < 
n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `FormalMultilinearSeries.removeZero_of_pos`：removeZero_of_pos (p : Formal
MultilinearSeries 𝕜 E F) {n : Nat} (h : 0 < n) : p.removeZero n = p n
· 使用定理 `Composition.length_pos_of_pos`：∀ {n : ℕ} (c : Composition n), 0 < n → 0 
< c.length

--- 原说明 ---
Only `0`-th coefficient of `q.comp p` depends on `q 0`.
-/
theorem removeZero_comp_of_pos (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : 0 < n) :
    q.removeZero.comp p n = q.comp p n := by
  ext v
  simp only [FormalMultilinearSeries.comp, compAlongComposition,
    ContinuousMultilinearMap.compAlongComposition_apply, sum_apply]
  refine Finset.sum_congr rfl fun c _hc => ?_
  rw [removeZero_of_pos _ (c.length_pos_of_pos hn)]

@[simp]
/-
**FormalMultilinearSeries.comp_removeZero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：comp_removeZero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinear
Series 𝕜 E F) : q.comp p.removeZero = q.comp p
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FormalMultilinearSeries.removeZero_applyComposition`：removeZero_applyCom
position (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n) : p.r
emoveZero.applyComposition c = p.applyCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_removeZero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    q.comp p.removeZero = q.comp p := by ext n; simp [FormalMultilinearSeries.comp]

end FormalMultilinearSeries

end Topological

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

namespace FormalMultilinearSeries

/-- The norm of `f.compAlongComposition p c` is controlled by the product of
the norms of the relevant bits of `f` and `p`. -/
/-
**FormalMultilinearSeries.compAlongComposition_bound** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：compAlongComposition_bound {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (
c : Composition n) (f : F [×c.length]->L[𝕜] G) (v : Fin n -> E) : ‖f.compAlongCo
mposition p c v‖ <= (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖
参数：p : FormalMultilinearSeries 𝕜 E F；c : Composition n；f : F [×c.length]->L[𝕜] G
；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Finset.univ_sigma_univ`：∀ {ι : Type u_1} {κ : ι → Type u_3} [inst : (i :
 ι) → Fintype (κ i)] [inst_1 : Fintype ι],   (Finset.univ.sigma fun x => Finset.
univ) = Fins…
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…

--- 原说明 ---
The norm of `f.compAlongComposition p c` is controlled by the product of
the norms of the relevant bits of `f` and `p`.
-/
theorem compAlongComposition_bound {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) (v : Fin n → E) :
    ‖f.compAlongComposition p c v‖ ≤ (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ :=
  calc
    ‖f.compAlongComposition p c v‖ = ‖f (p.applyComposition c v)‖ := rfl
    _ ≤ ‖f‖ * ∏ i, ‖p.applyComposition c v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖f‖ * ∏ i, ‖p (c.blocksFun i)‖ * ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      gcongr with i
      apply ContinuousMultilinearMap.le_opNorm
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) *
        ∏ i, ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      rw [Finset.prod_mul_distrib, mul_assoc]
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ := by
      rw [← c.blocksFinEquiv.prod_comp, ← Finset.univ_sigma_univ, Finset.prod_sigma]
      congr

/-- The norm of `q.compAlongComposition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
/-
**FormalMultilinearSeries.compAlongComposition_norm** 是 Mathlib 中的一个定理，位于命名空间 `F
ormalMultilinearSeries`。
形式化陈述：compAlongComposition_norm {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p
 : FormalMultilinearSeries 𝕜 E F) (c : Composition n) : ‖q.compAlongComposition 
p c‖ <= ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Compo
sition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `FormalMultilinearSeries.compAlongComposition_bound`：compAlongComposition
_bound {n : Nat} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) (f : F 
[×c.length]->L[𝕜] G) (v : Fin n -> E) : …

--- 原说明 ---
The norm of `q.compAlongComposition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`.
-/
theorem compAlongComposition_norm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖ ≤ ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)
/-
**FormalMultilinearSeries.compAlongComposition_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 
`FormalMultilinearSeries`。
形式化陈述：compAlongComposition_nnnorm {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) 
(p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) : ‖q.compAlongCompositio
n p c‖₊ <= ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Compo
sition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `FormalMultilinearSeries.compAlongComposition_norm`：compAlongComposition_
norm {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 
𝕜 E F) (c : Composition n) : ‖q.compAlo…
-/
theorem compAlongComposition_nnnorm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖₊ ≤ ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊ := by
  rw [← NNReal.coe_le_coe]; push_cast; exact q.compAlongComposition_norm p c

/-!
### The identity formal power series

We will now define the identity power series, and show that it is a neutral element for left and
right composition.
-/


section

variable (𝕜 E)

/-- The identity formal multilinear series, with all coefficients equal to `0` except for `n = 1`
where it is (the continuous multilinear version of) the identity. We allow an arbitrary
constant coefficient `x`. -/
/-
**FormalMultilinearSeries.id** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeries`
。
形式化陈述：(𝕜 : Type u_1) →   (E : Type u_2) →     [inst : NontriviallyNormedField 𝕜]
 →       [inst_1 : NormedAddCommGroup E] → [inst_2 : NormedSpace 𝕜 E] → E → Form
alMultilinearSeries 𝕜 E E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity formal multilinear series, with all coefficients equal to `0` excep
t for `n = 1`
where it is (the continuous multilinear version of) the identity. We allow an ar
bitrary
constant coefficient `x`.
-/
def id (x : E) : FormalMultilinearSeries 𝕜 E E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 E E).symm (ContinuousLinearMap.id 𝕜 E)
  | _ => 0
/-
**FormalMultilinearSeries.id_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (x : E) (v : Fin 0 → E), (
FormalMultilinearSeries.id 𝕜 E x 0) v = x
参数：𝕜 : Type u_1；E : Type u_2；x : E；v : Fin 0 → E；FormalMultilinearSeries.id 𝕜 E 
x 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem id_apply_zero (x : E) (v : Fin 0 → E) :
    (FormalMultilinearSeries.id 𝕜 E x) 0 v = x := rfl

/-- The first coefficient of `id 𝕜 E` is the identity. -/
@[simp]
/-
**FormalMultilinearSeries.id_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：id_apply_one (x : E) (v : Fin 1 -> E) : (FormalMultilinearSeries.id 𝕜 E x)
 1 v = v 0
参数：x : E；v : Fin 1 -> E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first coefficient of `id 𝕜 E` is the identity.
-/
theorem id_apply_one (x : E) (v : Fin 1 → E) : (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0 :=
  rfl

/-- The `n`th coefficient of `id 𝕜 E` is the identity when `n = 1`. We state this in a dependent
way, as it will often appear in this form. -/
/-
**FormalMultilinearSeries.id_apply_one'** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：id_apply_one' (x : E) {n : Nat} (h : n = 1) (v : Fin n -> E) : (id 𝕜 E x) 
n v = v ⟨0, h.symm ▸ zero_lt_one⟩
参数：x : E；h : n = 1；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.id_apply_one`：id_apply_one (x : E) (v : Fin 1 ->
 E) : (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0

--- 原说明 ---
The `n`th coefficient of `id 𝕜 E` is the identity when `n = 1`. We state this in
 a dependent
way, as it will often appear in this form.
-/
theorem id_apply_one' (x : E) {n : ℕ} (h : n = 1) (v : Fin n → E) :
    (id 𝕜 E x) n v = v ⟨0, h.symm ▸ zero_lt_one⟩ := by
  subst n
  apply id_apply_one

/-- For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition. -/
@[simp]
/-
**FormalMultilinearSeries.id_apply_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：id_apply_of_one_lt (x : E) {n : Nat} (h : 1 < n) : (FormalMultilinearSerie
s.id 𝕜 E x) n = 0
参数：x : E；h : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p

--- 原说明 ---
For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition.
-/
theorem id_apply_of_one_lt (x : E) {n : ℕ} (h : 1 < n) :
    (FormalMultilinearSeries.id 𝕜 E x) n = 0 := by
  match n with
    | 0 => contradiction
    | 1 => contradiction
    | n + 2 => rfl

end

@[simp]
/-
**FormalMultilinearSeries.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSe
ries`。
形式化陈述：comp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) : p.comp (id 𝕜 E x) = 
p
参数：p : FormalMultilinearSeries 𝕜 E F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Composition.ne_ones_iff`：ne_ones_iff {c : Composition n} : c != ones n ↔
 exists i in c.blocks, 1 < i
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Composition.blocks_length`：blocks_length : c.blocks.length = c.length
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `FormalMultilinearSeries.compAlongComposition_apply`：compAlongComposition
_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSerie
s 𝕜 E F) (c : Composition n) (v : Fin n …
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M
₁ i} (i : ι) (h : m i = 0) : f m = 0
· 使用定理 `FormalMultilinearSeries.id_apply_of_one_lt`：id_apply_of_one_lt (x : E) {
n : Nat} (h : 1 < n) : (FormalMultilinearSeries.id 𝕜 E x) n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Composition.ones_length`：ones_length (n : Nat) : (ones n).length = n
· 使用定理 `Composition.length_le`：length_le : c.length <= n
· 使用定理 `FormalMultilinearSeries.applyComposition_ones`：applyComposition_ones (p 
: FormalMultilinearSeries 𝕜 E F) (n : Nat) : p.applyComposition (Composition.one
s n) = fun v i => p 1 fun _ => v (F…
（共 34 条，此处仅展示前 30 条）
-/
theorem comp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) : p.comp (id 𝕜 E x) = p := by
  ext1 n
  dsimp [FormalMultilinearSeries.comp]
  rw [Finset.sum_eq_single (Composition.ones n)]
  · show compAlongComposition p (id 𝕜 E x) (Composition.ones n) = p n
    ext v
    rw [compAlongComposition_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComposition_ones]
    refine congr_arg v ?_
    rw [Fin.ext_iff, Fin.val_castLE, Fin.val_mk]
  · change
    ∀ b : Composition n,
      b ∈ Finset.univ → b ≠ Composition.ones n → compAlongComposition p (id 𝕜 E x) b = 0
    intro b _ hb
    obtain ⟨k, hk, lt_k⟩ : ∃ (k : ℕ), k ∈ Composition.blocks b ∧ 1 < k :=
      Composition.ne_ones_iff.1 hb
    obtain ⟨i, hi⟩ : ∃ (i : Fin b.blocks.length), b.blocks[i] = k :=
      List.get_of_mem hk
    let j : Fin b.length := ⟨i.val, b.blocks_length ▸ i.prop⟩
    have A : 1 < b.blocksFun j := by convert! lt_k
    ext v
    rw [compAlongComposition_apply, _root_.zero_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ j
    dsimp [applyComposition]
    rw [id_apply_of_one_lt _ _ _ A, _root_.zero_apply]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FormalMultilinearSeries.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSe
ries`。
形式化陈述：id_comp (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 -> E) : (id 𝕜 F (p
 0 v0)).comp p = p
参数：p : FormalMultilinearSeries 𝕜 E F；v0 : Fin 0 -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.comp_coeff_zero'`：comp_coeff_zero' (q : FormalMu
ltilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 -> E) : (q
.comp p) 0 v = q 0 fun _i => 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Composition.length_pos_of_pos`：∀ {n : ℕ} (c : Composition n), 0 < n → 0 
< c.length
· 使用定理 `FormalMultilinearSeries.compAlongComposition_apply`：compAlongComposition
_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSerie
s 𝕜 E F) (c : Composition n) (v : Fin n …
· 使用定理 `FormalMultilinearSeries.id_apply_of_one_lt`：id_apply_of_one_lt (x : E) {
n : Nat} (h : 1 < n) : (FormalMultilinearSeries.id 𝕜 E x) n = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Composition.single_length`：single_length {n : Nat} (h : 0 < n) : (single
 n h).length = 1
· 使用定理 `FormalMultilinearSeries.id_apply_one'`：id_apply_one' (x : E) {n : Nat} (
h : n = 1) (v : Fin n -> E) : (id 𝕜 E x) n v = v ⟨0, h.symm ▸ zero_lt_one⟩
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
（共 35 条，此处仅展示前 30 条）
-/
theorem id_comp (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 → E) :
    (id 𝕜 F (p 0 v0)).comp p = p := by
  ext1 n
  obtain rfl | n_pos := n.eq_zero_or_pos
  · ext v
    simp only [comp_coeff_zero', id_apply_zero]
    congr with i
    exact i.elim0
  · dsimp [FormalMultilinearSeries.comp]
    rw [Finset.sum_eq_single (Composition.single n n_pos)]
    · show compAlongComposition (id 𝕜 F (p 0 v0)) p (Composition.single n n_pos) = p n
      ext v
      rw [compAlongComposition_apply, id_apply_one' _ _ _ (Composition.single_length n_pos)]
      dsimp [applyComposition]
      refine p.congr rfl fun i him hin => congr_arg v <| ?_
      ext; simp
    · change
      ∀ b : Composition n, b ∈ Finset.univ → b ≠ Composition.single n n_pos →
        compAlongComposition (id 𝕜 F (p 0 v0)) p b = 0
      intro b _ hb
      have A : 1 < b.length := by
        have : b.length ≠ 1 := by simpa [Composition.eq_single_iff_length] using hb
        have : 0 < b.length := Composition.length_pos_of_pos b n_pos
        lia
      ext v
      rw [compAlongComposition_apply, id_apply_of_one_lt _ _ _ A, _root_.zero_apply,
        _root_.zero_apply]
    · simp

/-- Variant of `id_comp` in which the zero coefficient is given by an equality hypothesis instead
of a definitional equality. Useful for rewriting or simplifying out in some situations. -/
/-
**FormalMultilinearSeries.id_comp'** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearS
eries`。
形式化陈述：id_comp' (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 -> E) (h 
: x = p 0 v0) : (id 𝕜 F x).comp p = p
参数：p : FormalMultilinearSeries 𝕜 E F；x : F；v0 : Fin 0 -> E；h : x = p 0 v0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.id_comp`：id_comp (p : FormalMultilinearSeries 𝕜 
E F) (v0 : Fin 0 -> E) : (id 𝕜 F (p 0 v0)).comp p = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `id_comp` in which the zero coefficient is given by an equality hypot
hesis instead
of a definitional equality. Useful for rewriting or simplifying out in some situ
ations.
-/
theorem id_comp' (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 → E) (h : x = p 0 v0) :
    (id 𝕜 F x).comp p = p := by
  simp [h]

/-! ### Summability properties of the composition of formal power series -/


section

/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
/-
**FormalMultilinearSeries.comp_summable_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：comp_summable_nnreal (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultil
inearSeries 𝕜 E F) (hq : 0 < q.radius) (hp : 0 < p.radius) : exists r > (0 : Rea
l>=0), Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * 
r ^ i.1
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；hq : 0 < 
q.radius；hp : 0 < p.radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `FormalMultilinearSeries.nnnorm_mul_pow_le_of_lt_radius`：nnnorm_mul_pow_l
e_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>
=0∞) < p.radius) : exists C > 0, forall n, ‖…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `zero_lt_four`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 160 条，此处仅展示前 30 条）

--- 原说明 ---
If two formal multilinear series have positive radius of convergence, then the t
erms appearing
in the definition of their composition are also summable (when multiplied by a s
uitable positive
geometric term).
-/
theorem comp_summable_nnreal (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (hq : 0 < q.radius) (hp : 0 < p.radius) :
    ∃ r > (0 : ℝ≥0),
      Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 := by
  /- This follows from the fact that the growth rate of `‖qₙ‖` and `‖pₙ‖` is at most geometric,
    giving a geometric bound on each `‖q.compAlongComposition p op‖`, together with the
    fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hq) with ⟨rq, rq_pos, hrq⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hp) with ⟨rp, rp_pos, hrp⟩
  simp only [lt_min_iff, ENNReal.coe_lt_one_iff, ENNReal.coe_pos] at hrp hrq rp_pos rq_pos
  obtain ⟨Cq, _hCq0, hCq⟩ : ∃ Cq > 0, ∀ n, ‖q n‖₊ * rq ^ n ≤ Cq :=
    q.nnnorm_mul_pow_le_of_lt_radius hrq.2
  obtain ⟨Cp, hCp1, hCp⟩ : ∃ Cp ≥ 1, ∀ n, ‖p n‖₊ * rp ^ n ≤ Cp := by
    rcases p.nnnorm_mul_pow_le_of_lt_radius hrp.2 with ⟨Cp, -, hCp⟩
    exact ⟨max Cp 1, le_max_right _ _, fun n => (hCp n).trans (le_max_left _ _)⟩
  let r0 : ℝ≥0 := (4 * Cp)⁻¹
  have r0_pos : 0 < r0 := inv_pos.2 (mul_pos zero_lt_four (zero_lt_one.trans_le hCp1))
  set r : ℝ≥0 := rp * rq * r0
  have r_pos : 0 < r := mul_pos (mul_pos rp_pos rq_pos) r0_pos
  have I :
    ∀ i : Σ n : ℕ, Composition n, ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 ≤ Cq / 4 ^ i.1 := by
    rintro ⟨n, c⟩
    have A := calc
      ‖q c.length‖₊ * rq ^ n ≤ ‖q c.length‖₊ * rq ^ c.length :=
        mul_le_mul' le_rfl (pow_le_pow_of_le_one rq.2 hrq.1.le c.length_le)
      _ ≤ Cq := hCq _
    have B := calc
      (∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n = ∏ i, ‖p (c.blocksFun i)‖₊ * rp ^ c.blocksFun i := by
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
      _ ≤ ∏ _i : Fin c.length, Cp := Finset.prod_le_prod' fun i _ => hCp _
      _ = Cp ^ c.length := by simp
      _ ≤ Cp ^ n := pow_right_mono₀ hCp1 c.length_le
    calc
      ‖q.compAlongComposition p c‖₊ * r ^ n ≤
          (‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) * r ^ n := by
        grw [q.compAlongComposition_nnnorm p c]
      _ = ‖q c.length‖₊ * rq ^ n * ((∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n) * r0 ^ n := by
        ring
      _ ≤ Cq * Cp ^ n * r0 ^ n := mul_le_mul' (mul_le_mul' A B) le_rfl
      _ = Cq / 4 ^ n := by
        simp only [r0]
        simp [field, mul_pow]
  refine ⟨r, r_pos, NNReal.summable_of_le I ?_⟩
  simp_rw [div_eq_mul_inv]
  refine Summable.mul_left _ ?_
  have : ∀ n : ℕ, HasSum (fun c : Composition n => (4 ^ n : ℝ≥0)⁻¹) (2 ^ (n - 1) / 4 ^ n) := by
    intro n
    convert! hasSum_fintype fun c : Composition n => (4 ^ n : ℝ≥0)⁻¹
    simp [Finset.card_univ, composition_card, div_eq_mul_inv]
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, (NNReal.summable_nat_add_iff 1).1 ?_⟩
  convert! (NNReal.summable_geometric (NNReal.div_lt_one_of_lt one_lt_two)).mul_left (1 / 4) using 1
  ext1 n
  rw [(this _).tsum_eq, add_tsub_cancel_right]
  simp [field, pow_succ, mul_pow, show (4 : ℝ≥0) = 2 * 2 by norm_num]

end

/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all compositions. -/
/-
**FormalMultilinearSeries.le_comp_radius_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：le_comp_radius_of_summable (q : FormalMultilinearSeries 𝕜 F G) (p : Formal
MultilinearSeries 𝕜 E F) (r : Real>=0) (hr : Summable fun i : Σ n, Composition n
 => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1) : (r : Real>=0∞) <= (q.comp p).ra
dius
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；r : Real>
=0；hr : Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ *
 r ^ i.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound_nnreal`：le_radius_of_bound_nn
real (C : Real>=0) {r : Real>=0} (h : forall n : Nat, ‖p n‖₊ * r ^ n <= C) : (r 
: Real>=0∞) <= p.radius
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `nnnorm_sum_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAddComm
Group E] (s : Finset ι) (f : ι → E),   ‖∑ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NNReal.tsum_comp_le_tsum_of_inj`：tsum_comp_le_tsum_of_inj {β : Type*} {f
 : α -> Real>=0} (hf : Summable f) {i : β -> α} (hi : Function.Injective i) : (∑
' x, f (i x)) <= ∑' x…
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)

--- 原说明 ---
Bounding below the radius of the composition of two formal multilinear series as
suming
summability over all compositions.
-/
theorem le_comp_radius_of_summable (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (r : ℝ≥0)
    (hr : Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1) :
    (r : ℝ≥0∞) ≤ (q.comp p).radius := by
  refine
    le_radius_of_bound_nnreal _
      (∑' i : Σ n, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst) fun n => ?_
  calc
    ‖FormalMultilinearSeries.comp q p n‖₊ * r ^ n ≤
        ∑' c : Composition n, ‖compAlongComposition q p c‖₊ * r ^ n := by
      rw [tsum_fintype, ← Finset.sum_mul]
      exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
    _ ≤ ∑' i : Σ n : ℕ, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst :=
      NNReal.tsum_comp_le_tsum_of_inj hr sigma_mk_injective

/-!
### Composing analytic functions

Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, Composition n` of `q.compAlongComposition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`compPartialSumSource`), its target
(`compPartialSumTarget`) and the change of variables itself (`compChangeOfVariables`) before
giving the main statement in `comp_partialSum`. -/


/-- Source set in the change of variables to compute the composition of partial sums of formal
power series.
See also `comp_partialSum`. -/
/-
**FormalMultilinearSeries.compPartialSumSource** 是 Mathlib 中的一个定义，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：compPartialSumSource (m M N : Nat) : Finset (Σ n, Fin n -> Nat)
参数：m M N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Source set in the change of variables to compute the composition of partial sums
 of formal
power series.
See also `comp_partialSum`.
-/
def compPartialSumSource (m M N : ℕ) : Finset (Σ n, Fin n → ℕ) :=
  Finset.sigma (Finset.Ico m M) (fun n : ℕ => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N :)

@[simp]
/-
**FormalMultilinearSeries.mem_compPartialSumSource_iff** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：mem_compPartialSumSource_iff (m M N : Nat) (i : Σ n, Fin n -> Nat) : i in 
compPartialSumSource m M N ↔ (m <= i.1 ∧ i.1 < M) ∧ forall a : Fin i.1, 1 <= i.2
 a ∧ i.2 a < N
参数：m M N : Nat；i : Σ n, Fin n -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_compPartialSumSource_iff (m M N : ℕ) (i : Σ n, Fin n → ℕ) :
    i ∈ compPartialSumSource m M N ↔
      (m ≤ i.1 ∧ i.1 < M) ∧ ∀ a : Fin i.1, 1 ≤ i.2 a ∧ i.2 a < N := by
  simp only [compPartialSumSource, Finset.mem_Ico, Fintype.mem_piFinset, Finset.mem_sigma]

/-- Change of variables appearing to compute the composition of partial sums of formal
power series -/
/-
**FormalMultilinearSeries.compChangeOfVariables** 是 Mathlib 中的一个定义，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：compChangeOfVariables (m M N : Nat) (i : Σ n, Fin n -> Nat) (hi : i in com
pPartialSumSource m M N) : Σ n, Composition n
参数：m M N : Nat；i : Σ n, Fin n -> Nat；hi : i in compPartialSumSource m M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change of variables appearing to compute the composition of partial sums of form
al
power series
-/
def compChangeOfVariables (m M N : ℕ) (i : Σ n, Fin n → ℕ) (hi : i ∈ compPartialSumSource m M N) :
    Σ n, Composition n := by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine ⟨∑ j, f j, ofFn fun a => f a, fun {i} hi' => ?_, by simp [sum_ofFn]⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin n, f j = i := by rwa [mem_ofFn', Set.mem_range] at hi'
  exact (hi.2 j).1

@[simp]
/-
**FormalMultilinearSeries.compChangeOfVariables_length** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：compChangeOfVariables_length (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i
 in compPartialSumSource m M N) : Composition.length (compChangeOfVariables m M 
N i hi).2 = i.1
参数：m M N : Nat；hi : i in compPartialSumSource m M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compChangeOfVariables_length (m M N : ℕ) {i : Σ n, Fin n → ℕ}
    (hi : i ∈ compPartialSumSource m M N) :
    Composition.length (compChangeOfVariables m M N i hi).2 = i.1 := by
  rcases i with ⟨k, blocks_fun⟩
  dsimp [compChangeOfVariables]
  simp only [Composition.length, length_ofFn]
/-
**FormalMultilinearSeries.compChangeOfVariables_blocksFun** 是 Mathlib 中的一个定理，位于命
名空间 `FormalMultilinearSeries`。
形式化陈述：compChangeOfVariables_blocksFun (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi 
: i in compPartialSumSource m M N) (j : Fin i.1) : (compChangeOfVariables m M N 
i hi).2.blocksFun ⟨j, (compChangeOfVariables_length m M N hi).symm ▸ j.2⟩ = i.2 
j
参数：m M N : Nat；hi : i in compPartialSumSource m M N；j : Fin i.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_length`：compChangeOfVariab
les_length (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i in compPartialSumSource
 m M N) : Composition.length (compChangeOf…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compChangeOfVariables_blocksFun (m M N : ℕ) {i : Σ n, Fin n → ℕ}
    (hi : i ∈ compPartialSumSource m M N) (j : Fin i.1) :
    (compChangeOfVariables m M N i hi).2.blocksFun
        ⟨j, (compChangeOfVariables_length m M N hi).symm ▸ j.2⟩ =
      i.2 j := by
  rcases i with ⟨n, f⟩
  dsimp [Composition.blocksFun, Composition.blocks, compChangeOfVariables]
  simp only [List.getElem_ofFn]

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a set. -/
/-
**FormalMultilinearSeries.compPartialSumTargetSet** 是 Mathlib 中的一个定义，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：compPartialSumTargetSet (m M N : Nat) : Set (Σ n, Composition n)
参数：m M N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Target set in the change of variables to compute the composition of partial sums
 of formal
power series, here given a a set.
-/
def compPartialSumTargetSet (m M N : ℕ) : Set (Σ n, Composition n) :=
  {i | m ≤ i.2.length ∧ i.2.length < M ∧ ∀ j : Fin i.2.length, i.2.blocksFun j < N}
/-
**FormalMultilinearSeries.compPartialSumTargetSet_image_compPartialSumSource** 是
 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：compPartialSumTargetSet_image_compPartialSumSource (m M N : Nat) (i : Σ n,
 Composition n) (hi : i in compPartialSumTargetSet m M N) : exists (j : _) (hj :
 j in compPartialSumSource m M N), compChangeOfVariables m M N j hj = i
参数：m M N : Nat；i : Σ n, Composition n；hi : i in compPartialSumTargetSet m M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Composition.one_le_blocks'`：one_le_blocks' {i : Nat} (h : i < c.length) 
: 1 <= c.blocks[i]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Composition.sigma_eq_iff_blocks_eq`：sigma_eq_iff_blocks_eq {c : Σ n, Com
position n} {c' : Σ n, Composition n} : c = c' ↔ c.2.blocks = c'.2.blocks
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.ofFn_get`：∀ {α : Type u} (l : List α), List.ofFn l.get = l
-/
theorem compPartialSumTargetSet_image_compPartialSumSource (m M N : ℕ)
    (i : Σ n, Composition n) (hi : i ∈ compPartialSumTargetSet m M N) :
    ∃ (j : _) (hj : j ∈ compPartialSumSource m M N), compChangeOfVariables m M N j hj = i := by
  rcases i with ⟨n, c⟩
  refine ⟨⟨c.length, c.blocksFun⟩, ?_, ?_⟩
  · simp only [compPartialSumTargetSet, Set.mem_ofPred_eq] at hi
    simp only [mem_compPartialSumSource_iff, hi.left, hi.right, true_and, and_true]
    exact fun a => c.one_le_blocks' _
  · dsimp [compChangeOfVariables]
    rw [Composition.sigma_eq_iff_blocks_eq]
    simp only [Composition.blocksFun]
    conv_rhs => rw [← List.ofFn_get c.blocks]

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a finset.
See also `comp_partialSum`. -/
/-
**FormalMultilinearSeries.compPartialSumTarget** 是 Mathlib 中的一个定义，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：compPartialSumTarget (m M N : Nat) : Finset (Σ n, Composition n)
参数：m M N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Target set in the change of variables to compute the composition of partial sums
 of formal
power series, here given a a finset.
See also `comp_partialSum`.
-/
def compPartialSumTarget (m M N : ℕ) : Finset (Σ n, Composition n) :=
  Set.Finite.toFinset <|
    ((Finset.finite_toSet _).dependent_image _).subset <|
      compPartialSumTargetSet_image_compPartialSumSource m M N

@[simp]
/-
**FormalMultilinearSeries.mem_compPartialSumTarget_iff** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：mem_compPartialSumTarget_iff {m M N : Nat} {a : Σ n, Composition n} : a in
 compPartialSumTarget m M N ↔ m <= a.2.length ∧ a.2.length < M ∧ forall j : Fin 
a.2.length, a.2.blocksFun j < N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_compPartialSumTarget_iff {m M N : ℕ} {a : Σ n, Composition n} :
    a ∈ compPartialSumTarget m M N ↔
      m ≤ a.2.length ∧ a.2.length < M ∧ ∀ j : Fin a.2.length, a.2.blocksFun j < N := by
  simp [compPartialSumTarget, compPartialSumTargetSet]

/-- `compChangeOfVariables m M N` is a bijection between `compPartialSumSource m M N`
and `compPartialSumTarget m M N`, yielding equal sums for functions that correspond to each
other under the bijection. As `compChangeOfVariables m M N` is a dependent function, stating
that it is a bijection is not directly possible, but the consequence on sums can be stated
more easily. -/
/-
**FormalMultilinearSeries.compChangeOfVariables_sum** 是 Mathlib 中的一个定理，位于命名空间 `F
ormalMultilinearSeries`。
形式化陈述：compChangeOfVariables_sum {α : Type*} [AddCommMonoid α] (m M N : Nat) (f :
 (Σ n : Nat, Fin n -> Nat) -> α) (g : (Σ n, Composition n) -> α) (h : forall (e)
 (he : e in compPartialSumSource m M N), f e = g (compChangeOfVariables m M N e 
he)) : ∑ e in compPartialSumSource m M N, f e = ∑ e in compPartialSumTarget m M 
N, g e
参数：m M N : Nat；f : (Σ n : Nat, Fin n -> Nat) -> α；g : (Σ n, Composition n) -> α；
h : forall (e) (he : e in compPartialSumSource m M N), f e = g (compChangeOfVari
ables m M N e he)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FormalMultilinearSeries.mem_compPartialSumSource_iff`：mem_compPartialSum
Source_iff (m M N : Nat) (i : Σ n, Fin n -> Nat) : i in compPartialSumSource m M
 N ↔ (m <= i.1 ∧ i.1 < M) ∧ forall a : Fin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_length`：compChangeOfVariab
les_length (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i in compPartialSumSource
 m M N) : Composition.length (compChangeOf…
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_blocksFun`：compChangeOfVar
iables_blocksFun (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i in compPartialSum
Source m M N) (j : Fin i.1) : (compChangeOfVa…
· 使用定理 `FormalMultilinearSeries.compPartialSumTargetSet_image_compPartialSumSour
ce`：compPartialSumTargetSet_image_compPartialSumSource (m M N : Nat) (i : Σ n, C
omposition n) (hi : i in compPartialSumTargetSet m M N) : exists…

--- 原说明 ---
`compChangeOfVariables m M N` is a bijection between `compPartialSumSource m M N
`
and `compPartialSumTarget m M N`, yielding equal sums for functions that corresp
ond to each
other under the bijection. As `compChangeOfVariables m M N` is a dependent funct
ion, stating
that it is a bijection is not directly possible, but the consequence on sums can
 be stated
more easily.
-/
theorem compChangeOfVariables_sum {α : Type*} [AddCommMonoid α] (m M N : ℕ)
    (f : (Σ n : ℕ, Fin n → ℕ) → α) (g : (Σ n, Composition n) → α)
    (h : ∀ (e) (he : e ∈ compPartialSumSource m M N), f e = g (compChangeOfVariables m M N e he)) :
    ∑ e ∈ compPartialSumSource m M N, f e = ∑ e ∈ compPartialSumTarget m M N, g e := by
  apply Finset.sum_bij (compChangeOfVariables m M N)
  -- We should show that the correspondence we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `compPartialSumTarget m N N`
  · rintro ⟨k, blocks_fun⟩ H
    rw [mem_compPartialSumSource_iff] at H
    simp only [mem_compPartialSumTarget_iff, Composition.length, H.left,
      length_ofFn, true_and, compChangeOfVariables]
    intro j
    simp only [Composition.blocksFun, (H.right _).right, List.get_ofFn]
  -- 2 - show that the map is injective
  · rintro ⟨k, blocks_fun⟩ H ⟨k', blocks_fun'⟩ H' heq
    obtain rfl : k = k' := by
      have := (compChangeOfVariables_length m M N H).symm
      rwa [heq, compChangeOfVariables_length] at this
    congr
    funext i
    calc
      blocks_fun i = (compChangeOfVariables m M N _ H).2.blocksFun _ :=
        (compChangeOfVariables_blocksFun m M N H i).symm
      _ = (compChangeOfVariables m M N _ H').2.blocksFun _ := by
        grind
      _ = blocks_fun' i := compChangeOfVariables_blocksFun m M N H' i
  -- 3 - show that the map is surjective
  · intro i hi
    apply compPartialSumTargetSet_image_compPartialSumSource m M N i
    simpa [compPartialSumTarget] using hi
  -- 4 - show that the composition gives the `compAlongComposition` application
  · assumption

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
/-
**FormalMultilinearSeries.compPartialSumTarget_tendsto_prod_atTop** 是 Mathlib 中的
一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：compPartialSumTarget_tendsto_prod_atTop : Tendsto (fun (p : Nat × Nat) => 
compPartialSumTarget 0 p.1 p.2) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_finset`：∀ {α : Type u_3} {β : Type u_4} [inst : P
reorder β] {f : β → Finset α},   Monotone f → (∀ (x : α), ∃ n, x ∈ f n) → Filter
.Tendsto f Filter.a…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.bddAbove`：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (
s : Finset α), BddAbove ↑s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
The auxiliary set corresponding to the composition of partial sums asymptoticall
y contains
all possible compositions.
-/
theorem compPartialSumTarget_tendsto_prod_atTop :
    Tendsto (fun (p : ℕ × ℕ) => compPartialSumTarget 0 p.1 p.2) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro m n hmn a ha
    have : ∀ i, i < m.1 → i < n.1 := fun i hi => lt_of_lt_of_le hi hmn.1
    have : ∀ i, i < m.2 → i < n.2 := fun i hi => lt_of_lt_of_le hi hmn.2
    simp_all
  · rintro ⟨n, c⟩
    simp only [mem_compPartialSumTarget_iff]
    obtain ⟨n, hn⟩ : BddAbove ((Finset.univ.image fun i : Fin c.length => c.blocksFun i) : Set ℕ) :=
      Finset.bddAbove _
    refine
      ⟨max n c.length + 1, bot_le, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _), fun j =>
        lt_of_le_of_lt (le_trans ?_ (le_max_left _ _)) (lt_add_one _)⟩
    apply hn
    simp only [Finset.mem_image_of_mem, Finset.mem_coe, Finset.mem_univ]

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
/-
**FormalMultilinearSeries.compPartialSumTarget_tendsto_atTop** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：compPartialSumTarget_tendsto_atTop : Tendsto (fun N => compPartialSumTarge
t 0 N N) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `FormalMultilinearSeries.compPartialSumTarget_tendsto_prod_atTop`：compPar
tialSumTarget_tendsto_prod_atTop : Tendsto (fun (p : Nat × Nat) => compPartialSu
mTarget 0 p.1 p.2) atTop atTop
· 使用定理 `Filter.tendsto_atTop_diagonal`：tendsto_atTop_diagonal [Preorder α] : Ten
dsto (fun a : α => (a, a)) atTop atTop

--- 原说明 ---
The auxiliary set corresponding to the composition of partial sums asymptoticall
y contains
all possible compositions.
-/
theorem compPartialSumTarget_tendsto_atTop :
    Tendsto (fun N => compPartialSumTarget 0 N N) atTop atTop := by
  apply Tendsto.comp compPartialSumTarget_tendsto_prod_atTop tendsto_atTop_diagonal

/-- Composing the partial sums of two multilinear series coincides with the sum over all
compositions in `compPartialSumTarget 0 N N`. This is precisely the motivation for the
definition of `compPartialSumTarget`. -/
/-
**FormalMultilinearSeries.comp_partialSum** 是 Mathlib 中的一个定理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：comp_partialSum (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinear
Series 𝕜 E F) (M N : Nat) (z : E) : q.partialSum M (∑ i in Finset.Ico 1 N, p i f
un _j => z) = ∑ i in compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fu
n _j => z
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；M N : Nat
；z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_sum`：compChangeOfVariables
_sum {α : Type*} [AddCommMonoid α] (m M N : Nat) (f : (Σ n : Nat, Fin n -> Nat) 
-> α) (g : (Σ n, Composition n) -> α) (…
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_length`：compChangeOfVariab
les_length (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i in compPartialSumSource
 m M N) : Composition.length (compChangeOf…
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `FormalMultilinearSeries.compChangeOfVariables_blocksFun`：compChangeOfVar
iables_blocksFun (m M N : Nat) {i : Σ n, Fin n -> Nat} (hi : i in compPartialSum
Source m M N) (j : Fin i.1) : (compChangeOfVa…
· 使用定理 `FormalMultilinearSeries.applyComposition.eq_1`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : CommRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : Ad
dCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousMultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] 
: (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)

--- 原说明 ---
Composing the partial sums of two multilinear series coincides with the sum over
 all
compositions in `compPartialSumTarget 0 N N`. This is precisely the motivation f
or the
definition of `compPartialSumTarget`.
-/
theorem comp_partialSum (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (M N : ℕ) (z : E) :
    q.partialSum M (∑ i ∈ Finset.Ico 1 N, p i fun _j => z) =
      ∑ i ∈ compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z := by
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H :
    (∑ n ∈ Finset.range M,
        ∑ r ∈ Fintype.piFinset fun i : Fin n => Finset.Ico 1 N,
          q n fun i : Fin n => p (r i) fun _j => z) =
      ∑ i ∈ compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z by
    simpa only [FormalMultilinearSeries.partialSum, ContinuousMultilinearMap.map_sum_finset] using H
  -- rewrite the first sum as a big sum over a sigma type, in the finset
  -- `compPartialSumTarget 0 N N`
  rw [Finset.range_eq_Ico, Finset.sum_sigma']
  -- use `compChangeOfVariables_sum`, saying that this change of variables respects sums
  apply compChangeOfVariables_sum 0 M N
  rintro ⟨k, blocks_fun⟩ H
  apply congr _ (compChangeOfVariables_length 0 M N H).symm
  intros
  rw [← compChangeOfVariables_blocksFun 0 M N H, applyComposition, Function.comp_def]

end FormalMultilinearSeries

open FormalMultilinearSeries

/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`, within
two sets `s` and `t` such that `f` maps `s` to `t`, then `g ∘ f` admits the power
series `q.comp p` at `x` within `s`. -/
/-
**HasFPowerSeriesWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinAt.comp {g : F -> G} {f : E -> F} {q : FormalMultilin
earSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {t : Set F} {s : Se
t E} (hg : HasFPowerSeriesWithinAt g q t (f x)) (hf : HasFPowerSeriesWithinAt f 
p s x) (hs : Set.MapsTo f s t) : HasFPowerSeriesWithinAt (g ∘ f) (q.comp p) s x
参数：hg : HasFPowerSeriesWithinAt g q t (f x)；hf : HasFPowerSeriesWithinAt f p s x
；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.comp_summable_nnreal`：comp_summable_nnreal (q : 
FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (hq : 0 < q.r
adius) (hp : 0 < p.radius) : exist…
· 使用定理 `HasFPowerSeriesWithinOnBall.radius_pos`：HasFPowerSeriesWithinOnBall.radi
us_pos (hf : HasFPowerSeriesWithinOnBall f p s x r) : 0 < p.radius
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `AnalyticWithinAt.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGro
up E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt`：HasFPowerSeriesWithinOnBal
l.analyticWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) : AnalyticWithin
At 𝕜 f s x
· 使用定理 `Set.MapsTo.insert`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β} {f : α → β},   Set.MapsTo f s t → ∀ (x : α), Set.MapsTo f (insert x s) (inser
t (f x)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff : s in 𝓝[t] x ↔ exists ε 
> 0, eball x ε inter t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `FormalMultilinearSeries.le_comp_radius_of_summable`：le_comp_radius_of_su
mmable (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (
r : Real>=0) (hr : Summable fun i : Σ n,…
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
If two functions `g` and `f` have power series `q` and `p` respectively at `f x`
 and `x`, within
two sets `s` and `t` such that `f` maps `s` to `t`, then `g ∘ f` admits the powe
r
series `q.comp p` at `x` within `s`.
-/
theorem HasFPowerSeriesWithinAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E} {t : Set F} {s : Set E}
    (hg : HasFPowerSeriesWithinAt g q t (f x)) (hf : HasFPowerSeriesWithinAt f p s x)
    (hs : Set.MapsTo f s t) : HasFPowerSeriesWithinAt (g ∘ f) (q.comp p) s x := by
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
    of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩
  rcases hf with ⟨rf, Hf⟩
  -- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`.
  rcases q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos with ⟨r, r_pos : 0 < r, hr⟩
  /- We will consider `y` which is smaller than `r` and `rf`, and also small enough that
    `f (x + y)` is close enough to `f x` to be in the disk where `g` is well behaved. Let
    `min (r, rf, δ)` be this new radius. -/
  obtain ⟨δ, δpos, hδ⟩ :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ {z : E}, z ∈ insert x s ∩ Metric.eball x δ
      → f z ∈ insert (f x) t ∩ Metric.eball (f x) rg := by
    have : insert (f x) t ∩ Metric.eball (f x) rg ∈ 𝓝[insert (f x) t] (f x) := by
      apply inter_mem_nhdsWithin
      exact Metric.eball_mem_nhds _ Hg.r_pos
    have := Hf.analyticWithinAt.continuousWithinAt_insert.tendsto_nhdsWithin (hs.insert x) this
    rcases EMetric.mem_nhdsWithin_iff.1 this with ⟨δ, δpos, Hδ⟩
    exact ⟨δ, δpos, fun {z} hz => Hδ (by rwa [Set.inter_comm])⟩
  let rf' := min rf δ
  have min_pos : 0 < min rf' r := by
    simp only [rf', r_pos, Hf.r_pos, δpos, lt_min_iff, ENNReal.coe_pos, and_self_iff]
  /- We will show that `g ∘ f` admits the power series `q.comp p` in the disk of
    radius `min (r, rf', δ)`. -/
  refine ⟨min rf' r, ?_⟩
  refine
    ⟨le_trans (min_le_right rf' r) (FormalMultilinearSeries.le_comp_radius_of_summable q p r hr),
      min_pos, fun {y} h'y hy ↦ ?_⟩
  /- Let `y` satisfy `‖y‖ < min (r, rf', δ)`. We want to show that `g (f (x + y))` is the sum of
    `q.comp p` applied to `y`. -/
  -- First, check that `y` is small enough so that estimates for `f` and `g` apply.
  have y_mem : y ∈ Metric.eball (0 : E) rf :=
    (Metric.eball_subset_eball (le_trans (min_le_left _ _) (min_le_left _ _))) hy
  have fy_mem : f (x + y) ∈ insert (f x) t ∩ Metric.eball (f x) rg := by
    apply hδ
    have : y ∈ Metric.eball (0 : E) δ :=
      (Metric.eball_subset_eball (le_trans (min_le_left _ _) (min_le_right _ _))) hy
    simpa [-Set.mem_insert_iff, edist_eq_enorm_sub, h'y]
  /- Now the proof starts. To show that the sum of `q.comp p` at `y` is `g (f (x + y))`,
    we will write `q.comp p` applied to `y` as a big sum over all compositions.
    Since the sum is summable, to get its convergence it suffices to get
    the convergence along some increasing sequence of sets.
    We will use the sequence of sets `compPartialSumTarget 0 n n`,
    along which the sum is exactly the composition of the partial sums of `q` and `p`, by design.
    To show that it converges to `g (f (x + y))`, pointwise convergence would not be enough,
    but we have uniform convergence to save the day. -/
  -- First step: the partial sum of `p` converges to `f (x + y)`.
  have A : Tendsto (fun n ↦ (n, ∑ a ∈ Finset.Ico 1 n, p a fun _ ↦ y))
      atTop (atTop ×ˢ 𝓝 (f (x + y) - f x)) := by
    apply Tendsto.prodMk tendsto_id
    have L : ∀ᶠ n in atTop, (∑ a ∈ Finset.range n, p a fun _b ↦ y) - f x
        = ∑ a ∈ Finset.Ico 1 n, p a fun _b ↦ y := by
      rw [eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      symm
      rw [eq_sub_iff_add_eq', Finset.range_eq_Ico, ← Hf.coeff_zero fun _i => y,
        Finset.sum_eq_sum_Ico_succ_bot hn]
    have :
      Tendsto (fun n => (∑ a ∈ Finset.range n, p a fun _b => y) - f x) atTop
        (𝓝 (f (x + y) - f x)) :=
      (Hf.hasSum h'y y_mem).tendsto_sum_nat.sub tendsto_const_nhds
    exact Tendsto.congr' L this
  -- Second step: the composition of the partial sums of `q` and `p` converges to `g (f (x + y))`.
  have B : Tendsto (fun n => q.partialSum n (∑ a ∈ Finset.Ico 1 n, p a fun _b ↦ y)) atTop
      (𝓝 (g (f (x + y)))) := by
    -- we use the fact that the partial sums of `q` converge to `g (f (x + y))`, uniformly on a
    -- neighborhood of `f (x + y)`.
    have : Tendsto (fun (z : ℕ × F) ↦ q.partialSum z.1 z.2)
        (atTop ×ˢ 𝓝 (f (x + y) - f x)) (𝓝 (g (f x + (f (x + y) - f x)))) := by
      apply Hg.tendsto_partialSum_prod (y := f (x + y) - f x)
      · simpa [edist_eq_enorm_sub] using! fy_mem.2
      · simpa using! fy_mem.1
    simpa using! this.comp A
  -- Third step: the sum over all compositions in `compPartialSumTarget 0 n n` converges to
  -- `g (f (x + y))`. As this sum is exactly the composition of the partial sum, this is a direct
  -- consequence of the second step
  have C :
    Tendsto
      (fun n => ∑ i ∈ compPartialSumTarget 0 n n, q.compAlongComposition p i.2 fun _j => y)
      atTop (𝓝 (g (f (x + y)))) := by
    simpa [comp_partialSum] using! B
  -- Fourth step: the sum over all compositions is `g (f (x + y))`. This follows from the
  -- convergence along a subsequence proved in the third step, and the fact that the sum is Cauchy
  -- thanks to the summability properties.
  have D :
    HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (g (f (x + y))) :=
    haveI cau :
      CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i ∈ s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ ≤
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ ≤ ‖compAlongComposition q p c‖ * (r : ℝ) ^ n := by
          rw [Finset.prod_const, Finset.card_fin]
          gcongr
          rw [Metric.mem_eball, edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    tendsto_nhds_of_cauchySeq_of_subseq cau compPartialSumTarget_tendsto_atTop C
  -- Fifth step: the sum over `n` of `q.comp p n` can be expressed as a particular resummation of
  -- the sum over all compositions, by grouping together the compositions of the same
  -- integer `n`. The convergence of the whole sum therefore implies the convergence of the sum
  -- of `q.comp p n`
  have E : HasSum (fun n => (q.comp p) n fun _j => y) (g (f (x + y))) := by
    apply D.sigma
    intro n
    simp only [compAlongComposition_apply, FormalMultilinearSeries.comp, sum_apply]
    exact hasSum_fintype _
  rw [Function.comp_apply]
  exact E

/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`,
then `g ∘ f` admits the power series `q.comp p` at `x`. -/
/-
**HasFPowerSeriesAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.comp {g : F -> G} {f : E -> F} {q : FormalMultilinearSer
ies 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E} (hg : HasFPowerSeriesAt g
 q (f x)) (hf : HasFPowerSeriesAt f p x) : HasFPowerSeriesAt (g ∘ f) (q.comp p) 
x
参数：hg : HasFPowerSeriesAt g q (f x)；hf : HasFPowerSeriesAt f p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFPowerSeriesWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesWithinAt.comp`：HasFPowerSeriesWithinAt.comp {g : F -> G} 
{f : E -> F} {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 
E F} {x : E} {t : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If two functions `g` and `f` have power series `q` and `p` respectively at `f x`
 and `x`,
then `g ∘ f` admits the power series `q.comp p` at `x`.
-/
theorem HasFPowerSeriesAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hg : HasFPowerSeriesAt g q (f x)) (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt (g ∘ f) (q.comp p) x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf hg ⊢
  apply hg.comp hf (by simp)

/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, within
two sets `s` and `t` such that `f` maps `s` to `t`, then `g ∘ f` is analytic at `x` within `s`. -/
/-
**AnalyticWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {x : E} {t : Set F} {s : S
et E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : AnalyticWithinAt 𝕜 f s x) (h : S
et.MapsTo f s t) : AnalyticWithinAt 𝕜 (g ∘ f) s x
参数：hg : AnalyticWithinAt 𝕜 g t (f x)；hf : AnalyticWithinAt 𝕜 f s x；h : Set.MapsT
o f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesWithinAt.analyticWithinAt`：HasFPowerSeriesWithinAt.analyt
icWithinAt (hf : HasFPowerSeriesWithinAt f p s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesWithinAt.comp`：HasFPowerSeriesWithinAt.comp {g : F -> G} 
{f : E -> F} {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 
E F} {x : E} {t : …

--- 原说明 ---
If two functions `g` and `f` are analytic respectively at `f x` and `x`, within
two sets `s` and `t` such that `f` maps `s` to `t`, then `g ∘ f` is analytic at 
`x` within `s`.
-/
theorem AnalyticWithinAt.comp {g : F → G} {f : E → F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  let ⟨_q, hq⟩ := hg
  let ⟨_p, hp⟩ := hf
  exact (hq.comp hp h).analyticWithinAt

/-- Version of `AnalyticWithinAt.comp` where point equality is a separate hypothesis. -/
/-
**AnalyticWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} {t :
 Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t y) (hf : AnalyticWithinAt 𝕜 f s
 x) (h : Set.MapsTo f s t) (hy : f x = y) : AnalyticWithinAt 𝕜 (g ∘ f) s x
参数：hg : AnalyticWithinAt 𝕜 g t y；hf : AnalyticWithinAt 𝕜 f s x；h : Set.MapsTo f 
s t；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Version of `AnalyticWithinAt.comp` where point equality is a separate hypothesis
.
-/
theorem AnalyticWithinAt.comp_of_eq {g : F → G} {f : E → F} {y : F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t y) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t)
    (hy : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← hy] at hg
  exact hg.comp hf h
/-
**AnalyticOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {t : Set E} (hf : An
alyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) : AnalyticOn 𝕜 (f
 ∘ g) t
参数：hf : AnalyticOn 𝕜 f s；hg : AnalyticOn 𝕜 g t；h : Set.MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
-/
lemma AnalyticOn.comp {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp (hg x m) h

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
@[to_fun (attr := fun_prop)]
/-
**AnalyticAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg : AnalyticAt 𝕜 g (f 
x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
参数：hg : AnalyticAt 𝕜 g (f x)；hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g
 ∘ f` is
analytic at `x`.
-/
theorem AnalyticAt.comp {g : F → G} {f : E → F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
    (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← analyticWithinAt_univ] at hg hf ⊢
  apply hg.comp hf (by simp)

@[deprecated (since := "2026-01-24")] alias AnalyticAt.comp' := AnalyticAt.fun_comp

/-- Version of `AnalyticAt.comp` where point equality is a separate hypothesis. -/
@[to_fun]
/-
**AnalyticAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : Anal
yticAt 𝕜 g y) (hf : AnalyticAt 𝕜 f x) (hy : f x = y) : AnalyticAt 𝕜 (g ∘ f) x
参数：hg : AnalyticAt 𝕜 g y；hf : AnalyticAt 𝕜 f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Version of `AnalyticAt.comp` where point equality is a separate hypothesis.
-/
theorem AnalyticAt.comp_of_eq {g : F → G} {f : E → F} {y : F} {x : E} (hg : AnalyticAt 𝕜 g y)
    (hf : AnalyticAt 𝕜 f x) (hy : f x = y) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← hy] at hg
  exact hg.comp hf
@[deprecated (since := "2026-05-18")] alias AnalyticAt.comp_of_eq' := AnalyticAt.fun_comp_of_eq
/-
**AnalyticAt.comp_analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp_analyticWithinAt {g : F -> G} {f : E -> F} {x : E} {s : Se
t E} (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWithi
nAt 𝕜 (g ∘ f) s x
参数：hg : AnalyticAt 𝕜 g (f x)；hf : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem AnalyticAt.comp_analyticWithinAt {g : F → G} {f : E → F} {x : E} {s : Set E}
    (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← analyticWithinAt_univ] at hg
  exact hg.comp hf (Set.mapsTo_univ _ _)
/-
**AnalyticAt.comp_analyticWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.comp_analyticWithinAt_of_eq {g : F -> G} {f : E -> F} {x : E} {
y : F} {s : Set E} (hg : AnalyticAt 𝕜 g y) (hf : AnalyticWithinAt 𝕜 f s x) (h : 
f x = y) : AnalyticWithinAt 𝕜 (g ∘ f) s x
参数：hg : AnalyticAt 𝕜 g y；hf : AnalyticWithinAt 𝕜 f s x；h : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem AnalyticAt.comp_analyticWithinAt_of_eq {g : F → G} {f : E → F} {x : E} {y : F} {s : Set E}
    (hg : AnalyticAt 𝕜 g y) (hf : AnalyticWithinAt 𝕜 f s x) (h : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← h] at hg
  exact hg.comp_analyticWithinAt hf

/-- If two functions `g` and `f` are analytic respectively on `s.image f` and `s`, then `g ∘ f` is
analytic on `s`. -/
/-
**AnalyticOnNhd.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.comp' {s : Set E} {g : F -> G} {f : E -> F} (hg : AnalyticOn
Nhd 𝕜 g (s.image f)) (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (g ∘ f) s
参数：hg : AnalyticOnNhd 𝕜 g (s.image f)；hf : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If two functions `g` and `f` are analytic respectively on `s.image f` and `s`, t
hen `g ∘ f` is
analytic on `s`.
-/
theorem AnalyticOnNhd.comp' {s : Set E} {g : F → G} {f : E → F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
    (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (g ∘ f) s :=
  fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)
/-
**AnalyticOnNhd.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg :
 AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set.MapsTo f s t) : Analy
ticOnNhd 𝕜 (g ∘ f) s
参数：hg : AnalyticOnNhd 𝕜 g t；hf : AnalyticOnNhd 𝕜 f s；st : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.comp'`：AnalyticOnNhd.comp' {s : Set E} {g : F -> G} {f : E
 -> F} (hg : AnalyticOnNhd 𝕜 g (s.image f)) (hf : AnalyticOnNhd 𝕜 f s) : Analyti
cOnNhd 𝕜 …
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
-/
theorem AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F}
    (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set.MapsTo f s t) :
    AnalyticOnNhd 𝕜 (g ∘ f) s :=
  comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf
/-
**AnalyticOnNhd.comp_analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.comp_analyticOn {f : F -> G} {g : E -> F} {s : Set F} {t : S
et E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) 
: AnalyticOn 𝕜 (f ∘ g) t
参数：hf : AnalyticOnNhd 𝕜 f s；hg : AnalyticOn 𝕜 g t；h : Set.MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
-/
lemma AnalyticOnNhd.comp_analyticOn {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp_analyticWithinAt (hg x m)

/-- If two functions `g` and `f` have finite power series `q` and `p` respectively at `f x` and `x`,
then `g ∘ f` admits the finite power series `q.comp p` at `x`. -/
/-
**HasFiniteFPowerSeriesAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.comp {m n : Nat} {g : F -> G} {f : E -> F} {q : Fo
rmalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E} (hg : H
asFiniteFPowerSeriesAt g q (f x) m) (hf : HasFiniteFPowerSeriesAt f p x n) (hn :
 0 < n) : HasFiniteFPowerSeriesAt (g ∘ f) (q.comp p) x (m * n)
参数：hg : HasFiniteFPowerSeriesAt g q (f x) m；hf : HasFiniteFPowerSeriesAt f p x n
；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.comp`：HasFPowerSeriesAt.comp {g : F -> G} {f : E -> F}
 {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
 (hg : HasFP…
· 使用定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`：HasFiniteFPowerSeriesAt.hasFP
owerSeriesAt (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasFiniteFPowerSeriesAt.finite`：HasFiniteFPowerSeriesAt.finite (hf : Has
FiniteFPowerSeriesAt f p x n) : forall m : Nat, n <= m -> p m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.sum_blocksFun`：sum_blocksFun : ∑ i, c.blocksFun i = n
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Finset.sum_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → M} {s : Fins
et ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If two functions `g` and `f` have finite power series `q` and `p` respectively a
t `f x` and `x`,
then `g ∘ f` admits the finite power series `q.comp p` at `x`.
-/
theorem HasFiniteFPowerSeriesAt.comp {m n : ℕ} {g : F → G} {f : E → F}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hg : HasFiniteFPowerSeriesAt g q (f x) m) (hf : HasFiniteFPowerSeriesAt f p x n) (hn : 0 < n) :
    HasFiniteFPowerSeriesAt (g ∘ f) (q.comp p) x (m * n) := by
  rcases hg.hasFPowerSeriesAt.comp hf.hasFPowerSeriesAt with ⟨r, hr⟩
  refine ⟨r, hr, fun i hi ↦ ?_⟩
  apply Finset.sum_eq_zero
  rintro c -
  ext v
  simp only [compAlongComposition_apply, _root_.zero_apply]
  rcases le_or_gt m c.length with hc | hc
  · simp [hg.finite _ hc]
  obtain ⟨j, hj⟩ : ∃ j, n ≤ c.blocksFun j := by
    contrapose! hi
    rw [← c.sum_blocksFun]
    rcases eq_zero_or_pos c.length with h'c | h'c
    · have : ∑ j : Fin c.length, c.blocksFun j = 0 := by
        apply Finset.sum_eq_zero (fun j hj ↦ ?_)
        have := j.2
        grind
      rw [this]
      exact mul_pos (by grind) hn
    · calc ∑ j : Fin c.length, c.blocksFun j
      _ < ∑ j : Fin c.length, n := by
        apply Finset.sum_lt_sum (fun j hj ↦ (hi j).le)
        exact ⟨⟨0, h'c⟩, Finset.mem_univ _, hi _⟩
      _ = c.length * n := by simp
      _ ≤ m * n := by gcongr
  apply ContinuousMultilinearMap.map_coord_zero _ j
  simp [applyComposition, hf.finite _ hj]

/-- If two functions `g` and `f` are continuously polynomial respectively at `f x` and `x`,
then `g ∘ f` is continuously polynomial at `x`. -/
@[to_fun]
/-
**CPolynomialAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.comp {g : F -> G} {f : E -> F} {x : E} (hg : CPolynomialAt 𝕜
 g (f x)) (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (g ∘ f) x
参数：hg : CPolynomialAt 𝕜 g (f x)；hf : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFiniteFPowerSeriesAt.comp`：HasFiniteFPowerSeriesAt.comp {m n : Nat} {
g : F -> G} {f : E -> F} {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilin
earSeries 𝕜 E F} {…
· 使用定理 `HasFiniteFPowerSeriesAt.of_le`：HasFiniteFPowerSeriesAt.of_le {m n : Nat}
 (h : HasFiniteFPowerSeriesAt f p x n) (hmn : n <= m) : HasFiniteFPowerSeriesAt 
f p x m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
If two functions `g` and `f` are continuously polynomial respectively at `f x` a
nd `x`,
then `g ∘ f` is continuously polynomial at `x`.
-/
theorem CPolynomialAt.comp {g : F → G} {f : E → F} {x : E}
    (hg : CPolynomialAt 𝕜 g (f x)) (hf : CPolynomialAt 𝕜 f x) :
    CPolynomialAt 𝕜 (g ∘ f) x := by
  rcases hg with ⟨q, m, hm⟩
  rcases hf with ⟨p, n, hn⟩
  refine ⟨q.comp p, m * (n + 1), ?_⟩
  exact hm.comp (hn.of_le (Nat.le_succ n)) (Nat.zero_lt_succ n)

/-- Version of `CPolynomialAt.comp` where point equality is a separate hypothesis. -/
@[to_fun]
/-
**CPolynomialAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.comp_of_eq {g : F -> G} {f : E -> F} {y : F} {x : E} (hg : C
PolynomialAt 𝕜 g y) (hf : CPolynomialAt 𝕜 f x) (hy : f x = y) : CPolynomialAt 𝕜 
(g ∘ f) x
参数：hg : CPolynomialAt 𝕜 g y；hf : CPolynomialAt 𝕜 f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.comp`：CPolynomialAt.comp {g : F -> G} {f : E -> F} {x : E}
 (hg : CPolynomialAt 𝕜 g (f x)) (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (g 
∘ f) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Version of `CPolynomialAt.comp` where point equality is a separate hypothesis.
-/
theorem CPolynomialAt.comp_of_eq {g : F → G} {f : E → F} {y : F} {x : E} (hg : CPolynomialAt 𝕜 g y)
    (hf : CPolynomialAt 𝕜 f x) (hy : f x = y) : CPolynomialAt 𝕜 (g ∘ f) x := by
  rw [← hy] at hg
  exact hg.comp hf

/-- If two functions `g` and `f` are continuously polynomial respectively on `s.image f` and `s`,
then `g ∘ f` is continuously polynomial on `s`. -/
/-
**CPolynomialOn.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.comp' {s : Set E} {g : F -> G} {f : E -> F} (hg : CPolynomia
lOn 𝕜 g (s.image f)) (hf : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s
参数：hg : CPolynomialOn 𝕜 g (s.image f)；hf : CPolynomialOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.comp`：CPolynomialAt.comp {g : F -> G} {f : E -> F} {x : E}
 (hg : CPolynomialAt 𝕜 g (f x)) (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (g 
∘ f) x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If two functions `g` and `f` are continuously polynomial respectively on `s.imag
e f` and `s`,
then `g ∘ f` is continuously polynomial on `s`.
-/
theorem CPolynomialOn.comp' {s : Set E} {g : F → G} {f : E → F} (hg : CPolynomialOn 𝕜 g (s.image f))
    (hf : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s :=
  fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)
/-
**CPolynomialOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg :
 CPolynomialOn 𝕜 g t) (hf : CPolynomialOn 𝕜 f s) (st : Set.MapsTo f s t) : CPoly
nomialOn 𝕜 (g ∘ f) s
参数：hg : CPolynomialOn 𝕜 g t；hf : CPolynomialOn 𝕜 f s；st : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.comp'`：CPolynomialOn.comp' {s : Set E} {g : F -> G} {f : E
 -> F} (hg : CPolynomialOn 𝕜 g (s.image f)) (hf : CPolynomialOn 𝕜 f s) : CPolyno
mialOn 𝕜 …
· 使用定理 `CPolynomialOn.mono`：CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn
 𝕜 f t) (hst : s subseteq t) : CPolynomialOn 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
-/
theorem CPolynomialOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F}
    (hg : CPolynomialOn 𝕜 g t) (hf : CPolynomialOn 𝕜 f s) (st : Set.MapsTo f s t) :
    CPolynomialOn 𝕜 (g ∘ f) s :=
  comp' (mono hg (Set.mapsTo_iff_image_subset.mp st)) hf

/-!
### Associativity of the composition of formal multilinear series

In this paragraph, we prove the associativity of the composition of formal power series.
By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : Composition n} (r.comp q) a.length (applyComposition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : Composition n} ∑_{b : Composition a.length}
  r b.length (applyComposition q b (applyComposition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : Composition n} r c.length (applyComposition (q.comp p) c v)
```
Here, `applyComposition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocksFun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocksFun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : Composition (c.blocksFun i)} q dᵢ.length (applyComposition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : Composition n} ∑_{d₀ : Composition (c.blocksFun 0),
  ..., d_{c.length - 1} : Composition (c.blocksFun (c.length - 1))}
  r c.length (fun i ↦ q dᵢ.length (applyComposition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 9]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.

This equivalence is called `Composition.sigmaEquivSigmaPi n` below.

We start with preliminary results on compositions, of a very specialized nature, then define the
equivalence `Composition.sigmaEquivSigmaPi n`, and we deduce finally the associativity of
composition of formal multilinear series in `FormalMultilinearSeries.comp_assoc`.
-/


namespace Composition

variable {n : ℕ}

/-- Rewriting equality in the dependent type `Σ (a : Composition n), Composition a.length)` in
non-dependent terms with lists, requiring that the blocks coincide. -/
/-
**Composition.sigma_composition_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sigma_composition_eq_iff (i j : Σ a : Composition n, Composition a.length)
 : i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks
参数：i j : Σ a : Composition n, Composition a.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y

--- 原说明 ---
Rewriting equality in the dependent type `Σ (a : Composition n), Composition a.l
ength)` in
non-dependent terms with lists, requiring that the blocks coincide.
-/
theorem sigma_composition_eq_iff (i j : Σ a : Composition n, Composition a.length) :
    i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks := by
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, ?_⟩
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rintro ⟨h, h'⟩
  obtain rfl : a = a' := by ext1; exact h
  obtain rfl : b = b' := by ext1; exact h'
  rfl

/-- Rewriting equality in the dependent type
`Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide. -/
/-
**Composition.sigma_pi_composition_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition
`。
形式化陈述：sigma_pi_composition_eq_iff (u v : Σ c : Composition n, forall i : Fin c.l
ength, Composition (c.blocksFun i)) : u = v ↔ (ofFn fun i => (u.2 i).blocks) = o
fFn fun i => (v.2 i).blocks
参数：u v : Σ c : Composition n, forall i : Fin c.length, Composition (c.blocksFun 
i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `Composition.ofFn_blocksFun`：ofFn_blocksFun : ofFn c.blocksFun = c.blocks
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)

--- 原说明 ---
Rewriting equality in the dependent type
`Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide.
-/
theorem sigma_pi_composition_eq_iff
    (u v : Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i)) :
    u = v ↔ (ofFn fun i => (u.2 i).blocks) = ofFn fun i => (v.2 i).blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases u with ⟨a, b⟩
  rcases v with ⟨a', b'⟩
  dsimp at H
  obtain rfl : a = a' := by
    ext1
    have :
      map List.sum (ofFn fun i : Fin (Composition.length a) => (b i).blocks) =
        map List.sum (ofFn fun i : Fin (Composition.length a') => (b' i).blocks) := by
      rw [H]
    simp only [map_ofFn] at this
    change
      (ofFn fun i : Fin (Composition.length a) => (b i).blocks.sum) =
        ofFn fun i : Fin (Composition.length a') => (b' i).blocks.sum at this
    simpa [Composition.blocks_sum, Composition.ofFn_blocksFun] using this
  ext1
  · rfl
  · simp only [heq_eq_eq, ofFn_inj] at H ⊢
    ext1 i
    ext1
    exact congrFun H i

/-- When `a` is a composition of `n` and `b` is a composition of `a.length`, `a.gather b` is the
composition of `n` obtained by gathering all the blocks of `a` corresponding to a block of `b`.
For instance, if `a = [6, 5, 3, 5, 2]` and `b = [2, 3]`, one should gather together
the first two blocks of `a` and its last three blocks, giving `a.gather b = [11, 10]`. -/
/-
**Composition.gather** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：gather (a : Composition n) (b : Composition a.length) : Composition n wher
e blocks
参数：a : Composition n；b : Composition a.length。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `a` is a composition of `n` and `b` is a composition of `a.length`, `a.gath
er b` is the
composition of `n` obtained by gathering all the blocks of `a` corresponding to 
a block of `b`.
For instance, if `a = [6, 5, 3, 5, 2]` and `b = [2, 3]`, one should gather toget
her
the first two blocks of `a` and its last three blocks, giving `a.gather b = [11,
 10]`.
-/
def gather (a : Composition n) (b : Composition a.length) : Composition n where
  blocks := (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map]
    intro j hj
    suffices H : ∀ i ∈ j, 1 ≤ i from calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ ≤ j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks
    rw [← a.blocks.flatten_splitWrtComposition b]
    exact mem_flatten_of_mem hj hi
  blocks_sum := by rw [← sum_flatten, flatten_splitWrtComposition, a.blocks_sum]
/-
**Composition.length_gather** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：length_gather (a : Composition n) (b : Composition a.length) : length (a.g
ather b) = b.length
参数：a : Composition n；b : Composition a.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_splitWrtComposition`：length_splitWrtComposition (l : List α)
 (c : Composition n) : length (l.splitWrtComposition c) = c.length
-/
theorem length_gather (a : Composition n) (b : Composition a.length) :
    length (a.gather b) = b.length :=
  show (map List.sum (a.blocks.splitWrtComposition b)).length = b.blocks.length by
    rw [length_map, length_splitWrtComposition]

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary function used in the definition of `sigmaEquivSigmaPi` below, associating to
two compositions `a` of `n` and `b` of `a.length`, and an index `i` bounded by the length of
`a.gather b`, the subcomposition of `a` made of those blocks belonging to the `i`-th block of
`a.gather b`. -/
/-
**Composition.sigmaCompositionAux** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：sigmaCompositionAux (a : Composition n) (b : Composition a.length) (i : Fi
n (a.gather b).length) : Composition ((a.gather b).blocksFun i) where blocks
参数：a : Composition n；b : Composition a.length；i : Fin (a.gather b).length。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function used in the definition of `sigmaEquivSigmaPi` below, assoc
iating to
two compositions `a` of `n` and `b` of `a.length`, and an index `i` bounded by t
he length of
`a.gather b`, the subcomposition of `a` made of those blocks belonging to the `i
`-th block of
`a.gather b`.
-/
def sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin (a.gather b).length) : Composition ((a.gather b).blocksFun i) where
  blocks :=
    (a.blocks.splitWrtComposition b)[i.val]'(by
      rw [length_splitWrtComposition, ← length_gather]; exact i.2)
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.flatten_splitWrtComposition b]
        exact mem_flatten_of_mem (List.getElem_mem _) hi)
  blocks_sum := by simp [Composition.blocksFun, getElem_map, Composition.gather]
/-
**Composition.length_sigmaCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `Composition`
。
形式化陈述：length_sigmaCompositionAux (a : Composition n) (b : Composition a.length) 
(i : Fin b.length) : Composition.length (Composition.sigmaCompositionAux a b ⟨i,
 (length_gather a b).symm ▸ i.2⟩) = Composition.blocksFun b i
参数：a : Composition n；b : Composition a.length；i : Fin b.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_lt_of_le`：∀ {n b : ℕ} (i : Fin b), b ≤ n → ↑i < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_splitWrtComposition`：length_splitWrtComposition (l : List α)
 (c : Composition n) : length (l.splitWrtComposition c) = c.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.getElem_map_rev`：getElem_map_rev (f : α -> β) {l} {n : Nat} {h : n 
< l.length} : f l[n] = (map f l)[n]'((l.length_map f).symm ▸ h)
· 使用定理 `List.map_length_splitWrtComposition`：map_length_splitWrtComposition (l :
 List α) (c : Composition l.length) : map length (l.splitWrtComposition c) = c.b
locks
· 使用定理 `List.getElem_of_eq`：∀ {α : Type u_1} {l l' : List α} (h : l = l') {i : ℕ
} (w : i < l.length), l[i] = l'[i]
· 使用定理 `Composition.blocksFun.eq_1`：∀ {n : ℕ} (c : Composition n), c.blocksFun =
 c.blocks.get
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.get_eq_getElem`：get_eq_getElem? (l : List α) (i : Fin l.length) : l
.get i = l[i]?.get (by simp)
-/
theorem length_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) :
    Composition.length (Composition.sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩) =
      Composition.blocksFun b i :=
  show List.length ((splitWrtComposition a.blocks b)[i.1]) = blocksFun b i by
    rw [getElem_map_rev List.length, getElem_of_eq (map_length_splitWrtComposition _ _), blocksFun,
      get_eq_getElem]
/-
**Composition.blocksFun_sigmaCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `Compositi
on`。
形式化陈述：blocksFun_sigmaCompositionAux (a : Composition n) (b : Composition a.lengt
h) (i : Fin b.length) (j : Fin (blocksFun b i)) : blocksFun (sigmaCompositionAux
 a b ⟨i, (length_gather a b).symm ▸ i.2⟩) ⟨j, (length_sigmaCompositionAux a b i)
.symm ▸ j.2⟩ = blocksFun a (embedding b i j)
参数：a : Composition n；b : Composition a.length；i : Fin b.length；j : Fin (blocksFu
n b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.length_gather`：length_gather (a : Composition n) (b : Compos
ition a.length) : length (a.gather b) = b.length
· 使用定理 `Composition.length_sigmaCompositionAux`：length_sigmaCompositionAux (a : 
Composition n) (b : Composition a.length) (i : Fin b.length) : Composition.lengt
h (Composition.sigmaComposit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.blocksFun.eq_1`：∀ {n : ℕ} (c : Composition n), c.blocksFun =
 c.blocks.get
· 使用定理 `List.get_eq_getElem`：get_eq_getElem? (l : List α) (i : Fin l.length) : l
.get i = l[i]?.get (by simp)
· 使用定理 `List.getElem_splitWrtComposition`：getElem_splitWrtComposition (l : List 
α) (c : Composition n) (i : Nat) (h : i < (l.splitWrtComposition c).length) : (l
.splitWrtComposition c…
· 使用定理 `List.getElem_of_eq`：∀ {α : Type u_1} {l l' : List α} (h : l = l') {i : ℕ
} (w : i < l.length), l[i] = l'[i]
· 使用定理 `List.getElem_drop`：∀ {α : Type u_1} {xs : List α} {i j : ℕ} {h : j < (Li
st.drop i xs).length}, (List.drop i xs)[j] = xs[i + j]
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]
-/
theorem blocksFun_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) (j : Fin (blocksFun b i)) :
    blocksFun (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩)
        ⟨j, (length_sigmaCompositionAux a b i).symm ▸ j.2⟩ =
      blocksFun a (embedding b i j) := by
  unfold sigmaCompositionAux
  rw [blocksFun, get_eq_getElem, getElem_of_eq (getElem_splitWrtComposition _ _ _ _),
    getElem_drop, getElem_take]; rfl

/-- Auxiliary lemma to prove that the composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Grouping together some
blocks of `a` according to `b` as in `a.gather b`, one can compute the total size of the blocks
of `a` up to an index `sizeUpTo b i + j` (where the `j` corresponds to a set of blocks of `a`
that do not fill a whole block of `a.gather b`). The first part corresponds to a sum of blocks
in `a.gather b`, and the second one to a sum of blocks in the next block of
`sigmaCompositionAux a b`. This is the content of this lemma. -/
/-
**Composition.sizeUpTo_sizeUpTo_add** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_sizeUpTo_add (a : Composition n) (b : Composition a.length) {i j 
: Nat} (hi : i < b.length) (hj : j < blocksFun b ⟨i, hi⟩) : sizeUpTo a (sizeUpTo
 b i + j) = sizeUpTo (a.gather b) i + sizeUpTo (sigmaCompositionAux a b ⟨i, (len
gth_gather a b).symm ▸ hi⟩) j
参数：a : Composition n；b : Composition a.length；hi : i < b.length；hj : j < blocksF
un b ⟨i, hi⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.length_gather`：length_gather (a : Composition n) (b : Compos
ition a.length) : length (a.gather b) = b.length
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_splitWrtComposition`：length_splitWrtComposition (l : List α)
 (c : Composition n) : length (l.splitWrtComposition c) = c.length
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Composition.blocks_pos'`：blocks_pos' (i : Nat) (h : i < c.length) : 0 < 
c.blocks[i]
· 使用定理 `List.sum_take_succ`：∀ {M : Type u_4} [inst : AddMonoid M] (L : List M) (
i : ℕ) (p : i < L.length),   (List.take (i + 1) L).sum = (List.take i L).sum + L
[i]
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `List.monotone_sum_take`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : 
Preorder M] [CanonicallyOrderedAdd M] (L : List M),   Monotone fun i => (List.ta
ke i L).sum
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `List.getElem_splitWrtComposition`：getElem_splitWrtComposition (l : List 
α) (c : Composition n) (i : Nat) (h : i < (l.splitWrtComposition c).length) : (l
.splitWrtComposition c…
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `List.sum_append`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 + x2) 0]   [Std.Associative fun x1 x2 => x1 
+ x2]…
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Nat.instLawfulIdentityHAddOfNat`：Std.LawfulIdentity (fun x1 x2 => x1 + x
2) 0
· 使用定理 `Nat.instAssociativeHAdd`：Std.Associative fun x1 x2 => x1 + x2
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma to prove that the composition of formal multilinear series is as
sociative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Grouping 
together some
blocks of `a` according to `b` as in `a.gather b`, one can compute the total siz
e of the blocks
of `a` up to an index `sizeUpTo b i + j` (where the `j` corresponds to a set of 
blocks of `a`
that do not fill a whole block of `a.gather b`). The first part corresponds to a
 sum of blocks
in `a.gather b`, and the second one to a sum of blocks in the next block of
`sigmaCompositionAux a b`. This is the content of this lemma.
-/
theorem sizeUpTo_sizeUpTo_add (a : Composition n) (b : Composition a.length) {i j : ℕ}
    (hi : i < b.length) (hj : j < blocksFun b ⟨i, hi⟩) :
    sizeUpTo a (sizeUpTo b i + j) =
      sizeUpTo (a.gather b) i +
        sizeUpTo (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) j := by
  induction j with
  | zero =>
    change
      sum (take (b.blocks.take i).sum a.blocks) =
        sum (take i (map sum (splitWrtComposition a.blocks b)))
    induction i with
    | zero => rfl
    | succ i IH =>
      have A : i < b.length := Nat.lt_of_succ_lt hi
      have B : i < List.length (map List.sum (splitWrtComposition a.blocks b)) := by simp [A]
      have C : 0 < blocksFun b ⟨i, A⟩ := Composition.blocks_pos' _ _ _
      rw [sum_take_succ _ _ B, ← IH A C]
      have :
        take (sum (take i b.blocks)) a.blocks =
          take (sum (take i b.blocks)) (take (sum (take (i + 1) b.blocks)) a.blocks) := by
        rw [take_take, min_eq_left]
        apply monotone_sum_take _ (Nat.le_succ _)
      rw [this, getElem_map, getElem_splitWrtComposition, ←
        take_append_drop (sum (take i b.blocks)) (take (sum (take (Nat.succ i) b.blocks)) a.blocks),
        sum_append]
      congr
      rw [take_append_drop]
  | succ j IHj =>
    have A : j < blocksFun b ⟨i, hi⟩ := lt_trans (lt_add_one j) hj
    have B : j < length (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) := by
      convert! A; rw [← length_sigmaCompositionAux]
    have C : sizeUpTo b i + j < sizeUpTo b (i + 1) := by
      simp only [sizeUpTo_succ b hi, add_lt_add_iff_left]
      exact A
    have D : sizeUpTo b i + j < length a := lt_of_lt_of_le C (b.sizeUpTo_le _)
    have : sizeUpTo b i + Nat.succ j = (sizeUpTo b i + j).succ := rfl
    rw [this, sizeUpTo_succ _ D, IHj A, sizeUpTo_succ _ B]
    simp only [sigmaCompositionAux, add_assoc]
    rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _), getElem_drop, getElem_take]

/-- Natural equivalence between `(Σ (a : Composition n), Composition a.length)` and
`(Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i))`, that shows up as a
change of variables in the proof that composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Then `b` indicates how to
group together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of
blocks can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by
saying that each `dᵢ` is one single block. The map `⟨a, b⟩ → ⟨c, (d₀, ..., d_{a.length - 1})⟩` is
the direct map in the equiv.

Conversely, if one starts from `c` and the `dᵢ`s, one can join the `dᵢ`s to obtain a composition
`a` of `n`, and register the lengths of the `dᵢ`s in a composition `b` of `a.length`. This is the
inverse map of the equiv.
-/
/-
**Composition.sigmaEquivSigmaPi** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：sigmaEquivSigmaPi (n : Nat) : (Σ a : Composition n, Composition a.length) 
≃ Σ c : Composition n, forall i : Fin c.length, Composition (c.blocksFun i) wher
e toFun i
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural equivalence between `(Σ (a : Composition n), Composition a.length)` and
`(Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i))`, th
at shows up as a
change of variables in the proof that composition of formal multilinear series i
s associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Then `b` 
indicates how to
group together some blocks of `a`, giving altogether `b.length` blocks of blocks
. These blocks of
blocks can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition 
`c` of `n` by
saying that each `dᵢ` is one single block. The map `⟨a, b⟩ → ⟨c, (d₀, ..., d_{a.
length - 1})⟩` is
the direct map in the equiv.

Conversely, if one starts from `c` and the `dᵢ`s, one can join the `dᵢ`s to obta
in a composition
`a` of `n`, and register the lengths of the `dᵢ`s in a composition `b` of `a.len
gth`. This is the
inverse map of the equiv.
-/
def sigmaEquivSigmaPi (n : ℕ) :
    (Σ a : Composition n, Composition a.length) ≃
      Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i) where
  toFun i := ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{  blocks := (ofFn fun j => (i.2 j).blocks).flatten
        blocks_pos := by
          simp only [and_imp, List.mem_flatten, exists_imp, forall_mem_ofFn_iff]
          exact fun {i} j hj => Composition.blocks_pos _ hj
        blocks_sum := by simp [sum_ofFn, Composition.blocks_sum, Composition.sum_blocksFun] },
      { blocks := ofFn fun j => (i.2 j).length
        blocks_pos := by
          intro k hk
          refine ((forall_mem_ofFn_iff (P := fun i => 0 < i)).2 fun j => ?_) k hk
          exact Composition.length_pos_of_pos _ (Composition.blocks_pos' _ _ _)
        blocks_sum := by dsimp only [Composition.length]; simp [sum_ofFn] }⟩
  left_inv := by
    -- the fact that we have a left inverse is essentially `join_splitWrtComposition`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨a, b⟩
    rw [sigma_composition_eq_iff]
    dsimp
    constructor
    · conv_rhs =>
        rw [← flatten_splitWrtComposition a.blocks b, ← ofFn_get (splitWrtComposition a.blocks b)]
      have A : length (gather a b) = List.length (splitWrtComposition a.blocks b) := by
        simp only [length, gather, length_map, length_splitWrtComposition]
      congr! 2
      exact (Fin.heq_fun_iff A (α := List ℕ)).2 fun i => rfl
    · have B : Composition.length (Composition.gather a b) = List.length b.blocks :=
        Composition.length_gather _ _
      conv_rhs => rw [← ofFn_getElem (xs := b.blocks)]
      congr 1
      refine (Fin.heq_fun_iff B).2 fun i => ?_
      rw [sigmaCompositionAux, Composition.length, List.getElem_map_rev List.length,
        List.getElem_of_eq (map_length_splitWrtComposition _ _)]
  right_inv := by
    -- the fact that we have a right inverse is essentially `splitWrtComposition_join`,
    -- but we need to massage it to take care of the dependent setting.
    rintro ⟨c, d⟩
    have : map List.sum (ofFn fun i : Fin (Composition.length c) => (d i).blocks) = c.blocks := by
      simp [map_ofFn, Function.comp_def, Composition.blocks_sum, Composition.ofFn_blocksFun]
    rw [sigma_pi_composition_eq_iff]
    dsimp
    congr! 1
    · congr
      ext1
      dsimp [Composition.gather]
      rwa [splitWrtComposition_flatten]
      simp only [map_ofFn, Function.comp_def]
    · rw [Fin.heq_fun_iff]
      · intro i
        dsimp [Composition.sigmaCompositionAux]
        rw [getElem_of_eq (splitWrtComposition_flatten _ _ _)]
        · simp only [List.getElem_ofFn]
        · simp only [map_ofFn, Function.comp_def]
      · congr

end Composition

namespace FormalMultilinearSeries

open Composition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**FormalMultilinearSeries.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：comp_assoc (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSerie
s 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) : (r.comp q).comp p = r.comp (q.com
p p)
参数：r : FormalMultilinearSeries 𝕜 G H；q : FormalMultilinearSeries 𝕜 F G；p : Forma
lMultilinearSeries 𝕜 E F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Composition.length_gather`：length_gather (a : Composition n) (b : Compos
ition a.length) : length (a.gather b) = b.length
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Composition.length_sigmaCompositionAux`：length_sigmaCompositionAux (a : 
Composition n) (b : Composition a.length) (i : Fin b.length) : Composition.lengt
h (Composition.sigmaComposit…
· 使用定理 `Composition.blocksFun_sigmaCompositionAux`：blocksFun_sigmaCompositionAux
 (a : Composition n) (b : Composition a.length) (i : Fin b.length) (j : Fin (blo
cksFun b i)) : blocksFun (sigma…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Composition.sizeUpTo_sizeUpTo_add`：sizeUpTo_sizeUpTo_add (a : Compositio
n n) (b : Composition a.length) {i j : Nat} (hi : i < b.length) (hj : j < blocks
Fun b ⟨i, hi⟩) : sizeUp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.map_sum`：map_sum [DecidableEq ι] [forall i, Fin
type (α i)] : (f fun i => ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r i
)
-/
theorem comp_assoc (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) : (r.comp q).comp p = r.comp (q.comp p) := by
  ext n v
  /- First, rewrite the two compositions appearing in the theorem as two sums over complicated
    sigma types, as in the description of the proof above. -/
  let f : (Σ a : Composition n, Composition a.length) → H := fun c =>
    r c.2.length (applyComposition q c.2 (applyComposition p c.1 v))
  let g : (Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i)) → H := fun c =>
    r c.1.length fun i : Fin c.1.length =>
      q (c.2 i).length (applyComposition p (c.2 i) (v ∘ c.1.embedding i))
  suffices ∑ c, f c = ∑ c, g c by
    simpa +unfoldPartialApp only [FormalMultilinearSeries.comp, sum_apply,
      compAlongComposition_apply, Finset.sum_sigma', applyComposition,
      ContinuousMultilinearMap.map_sum]
  /- Now, we use `Composition.sigmaEquivSigmaPi n` to change
    variables in the second sum, and check that we get exactly the same sums. -/
  rw [← (sigmaEquivSigmaPi n).sum_comp]
  /- To check that we have the same terms, we should check that we apply the same component of
    `r`, and the same component of `q`, and the same component of `p`, to the same coordinate of
    `v`. This is true by definition, but at each step one needs to convince Lean that the types
    one considers are the same, using a suitable congruence lemma to avoid dependent type issues.
    This dance has to be done three times, one for `r`, one for `q` and one for `p`. -/
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  dsimp [sigmaEquivSigmaPi]
  -- check that the `r` components are the same. Based on `Composition.length_gather`
  apply r.congr (Composition.length_gather a b).symm
  intro i hi1 hi2
  -- check that the `q` components are the same. Based on `length_sigmaCompositionAux`
  apply q.congr (length_sigmaCompositionAux a b _).symm
  intro j hj1 hj2
  -- check that the `p` components are the same. Based on `blocksFun_sigmaCompositionAux`
  apply p.congr (blocksFun_sigmaCompositionAux a b _ _).symm
  intro k hk1 hk2
  -- finally, check that the coordinates of `v` one is using are the same. Based on
  -- `sizeUpTo_sizeUpTo_add`.
  refine congr_arg v (Fin.ext ?_)
  dsimp [Composition.embedding]
  rw [← add_assoc, ← sizeUpTo_sizeUpTo_add _ _ hi1 hj1]

end FormalMultilinearSeries

