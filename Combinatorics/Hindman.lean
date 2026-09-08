/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Topology.Algebra.Semigroup
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/

@[expose] public section


open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive (attr := instance_reducible)
/-- Addition of ultrafilters given by `∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`. -/]
/-
**Ultrafilter.mul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V

attribute [local instance] Ultrafilter.mul Ultrafilter.add

/-- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive /-- We could have taken this as the definition of `U + V`, but then we would have to
prove that it defines an ultrafilter. -/]
/-
**Ultrafilter.eventually_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M -> Pro
p) : (forallᶠ m in ↑(U * V), p m) ↔ forallᶠ m in U, forallᶠ m' in V, p (m * m')
参数：U V : Ultrafilter M；p : M -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl

/-- Semigroup structure on `Ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive (attr := instance_reducible)
/-- Additive semigroup structure on `Ultrafilter M` induced by an additive semigroup
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `M`. -/]
/-
**Ultrafilter.semigroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

-- We don't prove `continuous_mul_right`, because in general it is false!
@[to_additive]
/-
**Ultrafilter.continuous_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.continuous_mul_left {M} [Mul M] (V : Ultrafilter M) : Continuo
us (· * V)
参数：V : Ultrafilter M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.continuous_iff`：∀ {α : Type u} {β : 
Type u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {B : Set (Set β)}
,   TopologicalSpace.IsTopologicalBasis …
· 使用定理 `ultrafilterBasis_is_basis`：ultrafilterBasis_is_basis : TopologicalSpace.
IsTopologicalBasis (ultrafilterBasis α)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `ultrafilter_isOpen_basic`：ultrafilter_isOpen_basic (s : Set α) : IsOpen 
{ u : Ultrafilter α | s in u }
-/
theorem Ultrafilter.continuous_mul_left {M} [Mul M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun s ↦
    ultrafilter_isOpen_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }

namespace Hindman

/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
/-
**Hindman.FS** 是 Mathlib 中的一个归纳类型，位于命名空间 `Hindman`。
形式化陈述：{M : Type u_1} → [AddSemigroup M] → Stream' M → Set M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a 
nonempty
subsequence of `a`. We give a direct inductive definition instead of talking abo
ut subsequences.
-/
inductive FS {M} [AddSemigroup M] : Stream' M → Set M
  | head' (a : Stream' M) : FS a a.head
  | tail' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons' (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
/-
**Hindman.FP** 是 Mathlib 中的一个归纳类型，位于命名空间 `Hindman`。
形式化陈述：{M : Type u_1} → [Semigroup M] → Stream' M → Set M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the produ
ct of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking abo
ut subsequences.
-/
inductive FP {M} [Semigroup M] : Stream' M → Set M
  | head' (a : Stream' M) : FP a a.head
  | tail' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons' (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)

section Aliases

/-! Since the constructors for `FS` and `FP` cheat using the `Set M = M → Prop` defeq,
we provide match patterns that preserve the defeq correctly in their type. -/

variable {M} [Semigroup M] (a : Stream' M) (m : M) (h : FP a.tail m)

set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.head'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.head'`. -/]
/-
**Hindman.FP.head** 是 Mathlib 中的一个定义，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M), a.head ∈ Hindman.FP
 a
参数：a : Stream' M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FP.head : a.head ∈ FP a := FP.head' a
set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.tail'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.tail'`. -/]
/-
**Hindman.FP.tail** 是 Mathlib 中的一个定义，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M) (m : M), Hindman.FP 
a.tail m → m ∈ Hindman.FP a
参数：a : Stream' M；m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FP.tail : m ∈ FP a := FP.tail' a m h
set_option linter.defProp false in
/-- Constructor for `FP`. This is the preferred spelling over `FP.cons'`. -/
@[to_additive (attr := match_pattern)
  /-- Constructor for `FS`. This is the preferred spelling over `FS.cons'`. -/]
/-
**Hindman.FP.cons** 是 Mathlib 中的一个定义，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M) (m : M), Hindman.FP 
a.tail m → a.head * m ∈ Hindman.FP a
参数：a : Stream' M；m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FP.cons : a.head * m ∈ FP a := FP.cons' a m h

end Aliases

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive /-- If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
is obtained from a subsequence of `M` starting sufficiently late. -/]
/-
**Hindman.FP.mul** 是 Mathlib 中的一个定理，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] {a : Stream' M} {m : M},   m ∈ Hindm
an.FP a → ∃ n, ∀ m' ∈ Hindman.FP (Stream'.drop n a), m * m' ∈ Hindman.FP a
参数：Stream'.drop n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
    ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a := by
  induction hm with
  | head' a => exact ⟨1, fun m hm => FP.cons a m hm⟩
  | tail' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  | cons' a m _ ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')

@[to_additive exists_idempotent_ultrafilter_le_FS]
/-
**Hindman.exists_idempotent_ultrafilter_le_FP** 是 Mathlib 中的一个定理，位于命名空间 `Hindman
`。
形式化陈述：exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) : ex
ists U : Ultrafilter M, U * U = U ∧ forallᶠ m in U, m in FP a
参数：a : Stream' M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_idempotent_in_compact_subsemigroup`：exists_idempotent_in_compact_
subsemigroup {M} [Semigroup M] [TopologicalSpace M] [T2Space M] (continuous_cons
t_mul : forall r : M, Continuou…
· 使用定理 `Ultrafilter.continuous_mul_left`：Ultrafilter.continuous_mul_left {M} [Mu
l M] (V : Ultrafilter M) : Continuous (· * V)
· 使用定理 `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : Nat -> Set X) 
(htd : forall i, t (i + 1) subseteq t i) (htn : forall …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.drop_drop`：drop_drop (n m : Nat) (s : Stream' α) : drop n (drop 
m s) = drop (m + n) s
· 使用定理 `Stream'.tail_eq_drop`：tail_eq_drop (s : Stream' α) : tail s = drop 1 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_pure`：mem_pure {a : α} {s : Set α} : s in (pure a : Filter α)
 ↔ a in s
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `ultrafilter_isClosed_basic`：ultrafilter_isClosed_basic (s : Set α) : IsC
losed { u : Ultrafilter α | s in u }
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Ultrafilter.eventually_mul`：Ultrafilter.eventually_mul {M} [Mul M] (U V 
: Ultrafilter M) (p : M -> Prop) : (forallᶠ m in ↑(U * V), p m) ↔ forallᶠ m in U
, forallᶠ m' in …
· 使用定理 `Hindman.FP.mul`：∀ {M : Type u_1} [inst : Semigroup M] {a : Stream' M} {m
 : M},   m ∈ Hindman.FP a → ∃ n, ∀ m' ∈ Hindman.FP (Stream'.drop n a), m * m' ∈ 
Hind…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a := by
  let S : Set (Ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert! Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [← Stream'.drop_drop, ← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
      exact ⟨pure _, mem_pure.mpr <| FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_ofPred_eq, Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop, add_comm] using hm'

@[to_additive exists_FS_of_large]
/-
**Hindman.exists_FP_of_large** 是 Mathlib 中的一个定理，位于命名空间 `Hindman`。
形式化陈述：exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U =
 U) (s₀ : Set M) (sU : s₀ in U) : exists a, FP a subseteq s₀
参数：U : Ultrafilter M；U_idem : U * U = U；s₀ : Set M；sU : s₀ in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.nonempty_of_mem`：nonempty_of_mem (hs : s in f) : s.Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Stream'.corec_eq`：corec_eq (f : α -> β) (g : α -> α) (a : α) : corec f g
 a = f a :: corec f g (g a)
· 使用定理 `Stream'.head_cons`：head_cons (a : α) (s : Stream' α) : head (a::s) = a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Stream'.tail_cons`：tail_cons (a : α) (s : Stream' α) : tail (a::s) = s
-/
theorem exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
    (sU : s₀ ∈ U) : ∃ a, FP a ⊆ s₀ := by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again
  `U`-large, so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc.
  This gives the desired infinite sequence. -/
  have exists_elem : ∀ {s : Set M} (_hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m * m' ∈ s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s ∈ U } → M := fun p => (exists_elem p.property).some
  let succ : {s // s ∈ U} → {s // s ∈ U} := fun (p : {s // s ∈ U}) =>
        ⟨p.val ∩ {m : M | elem p * m ∈ p.val},
         inter_mem p.property
           (show (exists_elem p.property).some ∈ {m : M | ∀ᶠ (m' : M) in ↑U, m * m' ∈ p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices ∀ (a : Stream' M), ∀ m ∈ FP a, ∀ p, a = Stream'.corec elem succ p → m ∈ p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction h with
  | head' b =>
    rintro p rfl
    rw [Stream'.corec_eq, Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  | tail' b n h ih =>
    rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq, Stream'.tail_cons]
  | cons' b n h ih =>
    rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using! this
    rw [Stream'.corec_eq, Stream'.tail_cons]

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular /-- The strong form of **Hindman's theorem**: in any finite
cover of an FS-set, one the parts contains an FS-set. -/]
/-
**Hindman.FP_partition_regular** 是 Mathlib 中的一个定理，位于命名空间 `Hindman`。
形式化陈述：FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (
sfin : s.Finite) (scov : FP a subseteq ⋃₀ s) : exists c in s, exists b : Stream'
 M, FP b subseteq c
参数：a : Stream' M；s : Set (Set M)；sfin : s.Finite；scov : FP a subseteq ⋃₀ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hindman.exists_idempotent_ultrafilter_le_FP`：exists_idempotent_ultrafilt
er_le_FP {M} [Semigroup M] (a : Stream' M) : exists U : Ultrafilter M, U * U = U
 ∧ forallᶠ m in U, m in FP a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ultrafilter.finite_sUnion_mem_iff`：finite_sUnion_mem_iff {s : Set (Set α
)} (hs : s.Finite) : ⋃₀ s in f ↔ exists t in s, t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Hindman.exists_FP_of_large`：exists_FP_of_large {M} [Semigroup M] (U : Ul
trafilter M) (U_idem : U * U = U) (s₀ : Set M) (sU : s₀ in U) : exists a, FP a s
ubseteq s₀
-/
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ b : Stream' M, FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover /-- The weak form of **Hindman's theorem**: in any finite
cover of a nonempty additive semigroup, one of the parts contains an FS-set. -/]
/-
**Hindman.exists_FP_of_finite_cover** 是 Mathlib 中的一个定理，位于命名空间 `Hindman`。
形式化陈述：exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M))
 (sfin : s.Finite) (scov : ⊤ subseteq ⋃₀ s) : exists c in s, exists a : Stream' 
M, FP a subseteq c
参数：s : Set (Set M)；sfin : s.Finite；scov : ⊤ subseteq ⋃₀ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_idempotent_of_compact_t2_of_continuous_mul_left`：exists_idempoten
t_of_compact_t2_of_continuous_mul_left {M} [Nonempty M] [Semigroup M] [Topologic
alSpace M] [CompactSpace M] [T2Space M] (con…
· 使用定理 `Ultrafilter.instNonempty`：∀ {α : Type u} [Nonempty α], Nonempty (Ultrafi
lter α)
· 使用定理 `Ultrafilter.continuous_mul_left`：Ultrafilter.continuous_mul_left {M} [Mu
l M] (V : Ultrafilter M) : Continuous (· * V)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ultrafilter.finite_sUnion_mem_iff`：finite_sUnion_mem_iff {s : Set (Set α
)} (hs : s.Finite) : ⋃₀ s in f ↔ exists t in s, t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Hindman.exists_FP_of_large`：exists_FP_of_large {M} [Semigroup M] (U : Ul
trafilter M) (U_idem : U * U = U) (s₀ : Set M) (sU : s₀ in U) : exists a, FP a s
ubseteq s₀
-/
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ a : Stream' M, FP a ⊆ c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[to_additive FS_iter_tail_sub_FS]
/-
**Hindman.FP_drop_subset_FP** 是 Mathlib 中的一个定理，位于命名空间 `Hindman`。
形式化陈述：FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : Nat) : FP (a.drop
 n) subseteq FP a
参数：a : Stream' M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.drop_drop`：drop_drop (n m : Nat) (s : Stream' α) : drop n (drop 
m s) = drop (m + n) s
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : ℕ) : FP (a.drop n) ⊆ FP a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih

@[to_additive]
/-
**Hindman.FP.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M) (i : ℕ), a.get i ∈ H
indman.FP a
参数：a : Stream' M；i : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : ℕ) : a.get i ∈ FP a := by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)

@[to_additive]
/-
**Hindman.FP.mul_two** 是 Mathlib 中的一个定理，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M) (i j : ℕ), i < j → a
.get i * a.get j ∈ Hindman.FP a
参数：a : Stream' M；i j : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hindman.FP_drop_subset_FP`：FP_drop_subset_FP {M} [Semigroup M] (a : Stre
am' M) (n : Nat) : FP (a.drop n) subseteq FP a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.head_drop`：head_drop (a : Stream' α) (n : Nat) : (a.drop n).head
 = a.get n
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Hindman.FP.singleton`：∀ {M : Type u_1} [inst : Semigroup M] (a : Stream'
 M) (i : ℕ), a.get i ∈ Hindman.FP a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Stream'.get_drop`：get_drop (n m : Nat) (s : Stream' α) : get (drop m s) 
n = get s (m + n)
· 使用定理 `Stream'.tail_eq_drop`：tail_eq_drop (s : Stream' α) : tail s = drop 1 s
-/
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : ℕ) (ij : i < j) :
    a.get i * a.get j ∈ FP a := by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop, Stream'.get_drop, Stream'.get_drop] at this
  convert! this
  lia

@[to_additive]
/-
**Hindman.FP.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Hindman.FP`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] (a : Stream' M) (s : Finset ℕ), s.N
onempty → ∏ i ∈ s, a.get i ∈ Hindman.FP a
参数：a : Stream' M；s : Finset ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hindman.FP_drop_subset_FP`：FP_drop_subset_FP {M} [Semigroup M] (a : Stre
am' M) (n : Nat) : FP (a.drop n) subseteq FP a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.eraseInduction`：eraseInduction [DecidableEq α] {p : Finset α -> P
rop} (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α
) : p S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Stream'.head_drop`：head_drop (a : Stream' α) (n : Nat) : (a.drop n).head
 = a.get n
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Stream'.tail_eq_drop`：tail_eq_drop (s : Stream' α) : tail s = drop 1 s
· 使用定理 `Stream'.drop_drop`：drop_drop (n m : Nat) (s : Stream' α) : drop n (drop 
m s) = drop (m + n) s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Finset.min'_lt_of_mem_erase_min'`：∀ {α : Type u_2} [inst : LinearOrder α
] (s : Finset α) (H : s.Nonempty) [inst_1 : DecidableEq α] {a : α},   a ∈ s.eras
e (s.min' H) → s.min' …
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
-/
theorem FP.finsetProd {M} [CommMonoid M] (a : Stream' M) (s : Finset ℕ) (hs : s.Nonempty) :
    (s.prod fun i => a.get i) ∈ FP a := by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction s using Finset.eraseInduction with | H s ih => _
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs), ← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (s.min'_mem hs) h)
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
    rw [hd, ← Stream'.drop_drop, add_comm]
    apply FP_drop_subset_FP

@[deprecated (since := "2026-04-08")] alias FS.finset_sum := FS.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias FP.finset_prod := FP.finsetProd

end Hindman

